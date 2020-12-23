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
% DateTime   : Thu Dec  3 11:44:01 EST 2020

% Result     : Theorem 11.44s
% Output     : CNFRefutation 11.44s
% Verified   : 
% Statistics : Number of formulae       :  187 (6669 expanded)
%              Number of clauses        :  112 (1786 expanded)
%              Number of leaves         :   24 (1680 expanded)
%              Depth                    :   34
%              Number of atoms          :  349 (11260 expanded)
%              Number of equality atoms :  251 (6674 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f33,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f36,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f36])).

fof(f64,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f69])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f77,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f71])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f71])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f75,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f54,f72,f72])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) ),
    inference(definition_unfolding,[],[f53,f72,f72])).

fof(f65,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_421,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_10,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_147,plain,
    ( v1_relat_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_148,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_420,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_422,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_638,plain,
    ( k5_relat_1(sK0,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK0,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_422])).

cnf(c_887,plain,
    ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X0) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_420,c_638])).

cnf(c_1016,plain,
    ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0) ),
    inference(superposition,[status(thm)],[c_421,c_887])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_426,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2377,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1016,c_426])).

cnf(c_20,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_36,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_38,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_51,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1088,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1089,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_2888,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_20,c_38,c_51,c_1089])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_425,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2893,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)))))) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[status(thm)],[c_2888,c_425])).

cnf(c_639,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k1_xboole_0,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_420,c_422])).

cnf(c_3586,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK0),X0) = k5_relat_1(k1_xboole_0,k5_relat_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_639])).

cnf(c_4611,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k5_relat_1(X0,X1))) = k5_relat_1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_3586])).

cnf(c_6512,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k5_relat_1(sK0,X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_4611])).

cnf(c_6572,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_420,c_6512])).

cnf(c_7372,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6572,c_426])).

cnf(c_15683,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7372,c_20,c_38,c_51,c_1089])).

cnf(c_886,plain,
    ( k5_relat_1(k5_relat_1(sK0,sK0),X0) = k5_relat_1(sK0,k5_relat_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_638])).

cnf(c_956,plain,
    ( k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k5_relat_1(sK0,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_420,c_886])).

cnf(c_2375,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_426])).

cnf(c_8621,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2375,c_38,c_51])).

cnf(c_8622,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8621])).

cnf(c_8634,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)))))) = k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8622,c_425])).

cnf(c_14,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_423,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1184,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_423])).

cnf(c_16,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1209,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1184,c_16])).

cnf(c_2058,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1209,c_38,c_51])).

cnf(c_2059,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2058])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_429,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2064,plain,
    ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2059,c_429])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_427,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2135,plain,
    ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2064,c_427])).

cnf(c_2382,plain,
    ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_2135])).

cnf(c_7219,plain,
    ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2382,c_20])).

cnf(c_8663,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0))) = k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8634,c_7219])).

cnf(c_5,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_770,plain,
    ( k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_771,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_770,c_1,c_7])).

cnf(c_8664,plain,
    ( k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8663,c_5,c_771])).

cnf(c_8911,plain,
    ( k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_8664])).

cnf(c_11041,plain,
    ( k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8911,c_20])).

cnf(c_15687,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15683,c_11041])).

cnf(c_33,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_35,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_15691,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15687,c_35,c_38,c_51])).

cnf(c_15709,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))))) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_15691,c_425])).

cnf(c_1017,plain,
    ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_420,c_887])).

cnf(c_2374,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1017,c_426])).

cnf(c_7238,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2374,c_20,c_38,c_51,c_1089])).

cnf(c_7250,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))),k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)))))) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_7238,c_425])).

cnf(c_1183,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))),k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1017,c_423])).

cnf(c_1216,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1183,c_16])).

cnf(c_2067,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1216,c_20,c_38,c_51,c_1089])).

cnf(c_2072,plain,
    ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2067,c_429])).

cnf(c_2140,plain,
    ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2072,c_427])).

cnf(c_7270,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0))) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_7250,c_2140])).

cnf(c_7271,plain,
    ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7270,c_5,c_771])).

cnf(c_1544,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k2_relat_1(X1),k2_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_423,c_429])).

cnf(c_10305,plain,
    ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k2_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7271,c_1544])).

cnf(c_10435,plain,
    ( k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10305,c_16,c_7271])).

cnf(c_1187,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_423])).

cnf(c_2588,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1187,c_38,c_51])).

cnf(c_2589,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2588])).

cnf(c_1543,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_427,c_429])).

cnf(c_7026,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2589,c_1543])).

cnf(c_7038,plain,
    ( k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7026])).

cnf(c_10478,plain,
    ( k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10435,c_38,c_51,c_7038])).

cnf(c_15731,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_15709,c_10478])).

cnf(c_15732,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15731,c_5,c_771])).

cnf(c_17417,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15732,c_7271])).

cnf(c_19480,plain,
    ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(demodulation,[status(thm)],[c_17417,c_1016])).

cnf(c_13,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_424,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2319,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k1_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1016,c_424])).

cnf(c_3359,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k1_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2319,c_20,c_38,c_51,c_1089])).

cnf(c_19479,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17417,c_3359])).

cnf(c_19492,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19479,c_19480])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19494,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19492,c_17])).

cnf(c_19543,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19494,c_1543])).

cnf(c_24097,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_2893,c_19480,c_19543])).

cnf(c_9,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_871,plain,
    ( k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_878,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(light_normalisation,[status(thm)],[c_871,c_1,c_7])).

cnf(c_879,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_878,c_7])).

cnf(c_24098,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24097,c_5,c_879])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19482,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17417,c_18])).

cnf(c_19483,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_19482])).

cnf(c_24100,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24098,c_19483])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:34:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.44/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.44/2.00  
% 11.44/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.44/2.00  
% 11.44/2.00  ------  iProver source info
% 11.44/2.00  
% 11.44/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.44/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.44/2.00  git: non_committed_changes: false
% 11.44/2.00  git: last_make_outside_of_git: false
% 11.44/2.00  
% 11.44/2.00  ------ 
% 11.44/2.00  
% 11.44/2.00  ------ Input Options
% 11.44/2.00  
% 11.44/2.00  --out_options                           all
% 11.44/2.00  --tptp_safe_out                         true
% 11.44/2.00  --problem_path                          ""
% 11.44/2.00  --include_path                          ""
% 11.44/2.00  --clausifier                            res/vclausify_rel
% 11.44/2.00  --clausifier_options                    --mode clausify
% 11.44/2.00  --stdin                                 false
% 11.44/2.00  --stats_out                             all
% 11.44/2.00  
% 11.44/2.00  ------ General Options
% 11.44/2.00  
% 11.44/2.00  --fof                                   false
% 11.44/2.00  --time_out_real                         305.
% 11.44/2.00  --time_out_virtual                      -1.
% 11.44/2.00  --symbol_type_check                     false
% 11.44/2.00  --clausify_out                          false
% 11.44/2.00  --sig_cnt_out                           false
% 11.44/2.00  --trig_cnt_out                          false
% 11.44/2.00  --trig_cnt_out_tolerance                1.
% 11.44/2.00  --trig_cnt_out_sk_spl                   false
% 11.44/2.00  --abstr_cl_out                          false
% 11.44/2.00  
% 11.44/2.00  ------ Global Options
% 11.44/2.00  
% 11.44/2.00  --schedule                              default
% 11.44/2.00  --add_important_lit                     false
% 11.44/2.00  --prop_solver_per_cl                    1000
% 11.44/2.00  --min_unsat_core                        false
% 11.44/2.00  --soft_assumptions                      false
% 11.44/2.00  --soft_lemma_size                       3
% 11.44/2.00  --prop_impl_unit_size                   0
% 11.44/2.00  --prop_impl_unit                        []
% 11.44/2.00  --share_sel_clauses                     true
% 11.44/2.00  --reset_solvers                         false
% 11.44/2.00  --bc_imp_inh                            [conj_cone]
% 11.44/2.00  --conj_cone_tolerance                   3.
% 11.44/2.00  --extra_neg_conj                        none
% 11.44/2.00  --large_theory_mode                     true
% 11.44/2.00  --prolific_symb_bound                   200
% 11.44/2.00  --lt_threshold                          2000
% 11.44/2.00  --clause_weak_htbl                      true
% 11.44/2.00  --gc_record_bc_elim                     false
% 11.44/2.00  
% 11.44/2.00  ------ Preprocessing Options
% 11.44/2.00  
% 11.44/2.00  --preprocessing_flag                    true
% 11.44/2.00  --time_out_prep_mult                    0.1
% 11.44/2.00  --splitting_mode                        input
% 11.44/2.00  --splitting_grd                         true
% 11.44/2.00  --splitting_cvd                         false
% 11.44/2.00  --splitting_cvd_svl                     false
% 11.44/2.00  --splitting_nvd                         32
% 11.44/2.00  --sub_typing                            true
% 11.44/2.00  --prep_gs_sim                           true
% 11.44/2.00  --prep_unflatten                        true
% 11.44/2.00  --prep_res_sim                          true
% 11.44/2.00  --prep_upred                            true
% 11.44/2.00  --prep_sem_filter                       exhaustive
% 11.44/2.00  --prep_sem_filter_out                   false
% 11.44/2.00  --pred_elim                             true
% 11.44/2.00  --res_sim_input                         true
% 11.44/2.00  --eq_ax_congr_red                       true
% 11.44/2.00  --pure_diseq_elim                       true
% 11.44/2.00  --brand_transform                       false
% 11.44/2.00  --non_eq_to_eq                          false
% 11.44/2.00  --prep_def_merge                        true
% 11.44/2.00  --prep_def_merge_prop_impl              false
% 11.44/2.00  --prep_def_merge_mbd                    true
% 11.44/2.00  --prep_def_merge_tr_red                 false
% 11.44/2.00  --prep_def_merge_tr_cl                  false
% 11.44/2.00  --smt_preprocessing                     true
% 11.44/2.00  --smt_ac_axioms                         fast
% 11.44/2.00  --preprocessed_out                      false
% 11.44/2.00  --preprocessed_stats                    false
% 11.44/2.00  
% 11.44/2.00  ------ Abstraction refinement Options
% 11.44/2.00  
% 11.44/2.00  --abstr_ref                             []
% 11.44/2.00  --abstr_ref_prep                        false
% 11.44/2.00  --abstr_ref_until_sat                   false
% 11.44/2.00  --abstr_ref_sig_restrict                funpre
% 11.44/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.44/2.00  --abstr_ref_under                       []
% 11.44/2.00  
% 11.44/2.00  ------ SAT Options
% 11.44/2.00  
% 11.44/2.00  --sat_mode                              false
% 11.44/2.00  --sat_fm_restart_options                ""
% 11.44/2.00  --sat_gr_def                            false
% 11.44/2.00  --sat_epr_types                         true
% 11.44/2.00  --sat_non_cyclic_types                  false
% 11.44/2.00  --sat_finite_models                     false
% 11.44/2.00  --sat_fm_lemmas                         false
% 11.44/2.00  --sat_fm_prep                           false
% 11.44/2.00  --sat_fm_uc_incr                        true
% 11.44/2.00  --sat_out_model                         small
% 11.44/2.00  --sat_out_clauses                       false
% 11.44/2.00  
% 11.44/2.00  ------ QBF Options
% 11.44/2.00  
% 11.44/2.00  --qbf_mode                              false
% 11.44/2.00  --qbf_elim_univ                         false
% 11.44/2.00  --qbf_dom_inst                          none
% 11.44/2.00  --qbf_dom_pre_inst                      false
% 11.44/2.00  --qbf_sk_in                             false
% 11.44/2.00  --qbf_pred_elim                         true
% 11.44/2.00  --qbf_split                             512
% 11.44/2.00  
% 11.44/2.00  ------ BMC1 Options
% 11.44/2.00  
% 11.44/2.00  --bmc1_incremental                      false
% 11.44/2.00  --bmc1_axioms                           reachable_all
% 11.44/2.00  --bmc1_min_bound                        0
% 11.44/2.00  --bmc1_max_bound                        -1
% 11.44/2.00  --bmc1_max_bound_default                -1
% 11.44/2.00  --bmc1_symbol_reachability              true
% 11.44/2.00  --bmc1_property_lemmas                  false
% 11.44/2.00  --bmc1_k_induction                      false
% 11.44/2.00  --bmc1_non_equiv_states                 false
% 11.44/2.00  --bmc1_deadlock                         false
% 11.44/2.00  --bmc1_ucm                              false
% 11.44/2.00  --bmc1_add_unsat_core                   none
% 11.44/2.00  --bmc1_unsat_core_children              false
% 11.44/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.44/2.00  --bmc1_out_stat                         full
% 11.44/2.00  --bmc1_ground_init                      false
% 11.44/2.00  --bmc1_pre_inst_next_state              false
% 11.44/2.00  --bmc1_pre_inst_state                   false
% 11.44/2.00  --bmc1_pre_inst_reach_state             false
% 11.44/2.00  --bmc1_out_unsat_core                   false
% 11.44/2.00  --bmc1_aig_witness_out                  false
% 11.44/2.00  --bmc1_verbose                          false
% 11.44/2.00  --bmc1_dump_clauses_tptp                false
% 11.44/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.44/2.00  --bmc1_dump_file                        -
% 11.44/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.44/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.44/2.00  --bmc1_ucm_extend_mode                  1
% 11.44/2.00  --bmc1_ucm_init_mode                    2
% 11.44/2.00  --bmc1_ucm_cone_mode                    none
% 11.44/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.44/2.00  --bmc1_ucm_relax_model                  4
% 11.44/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.44/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.44/2.00  --bmc1_ucm_layered_model                none
% 11.44/2.00  --bmc1_ucm_max_lemma_size               10
% 11.44/2.00  
% 11.44/2.00  ------ AIG Options
% 11.44/2.00  
% 11.44/2.00  --aig_mode                              false
% 11.44/2.00  
% 11.44/2.00  ------ Instantiation Options
% 11.44/2.00  
% 11.44/2.00  --instantiation_flag                    true
% 11.44/2.00  --inst_sos_flag                         false
% 11.44/2.00  --inst_sos_phase                        true
% 11.44/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.44/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.44/2.00  --inst_lit_sel_side                     num_symb
% 11.44/2.00  --inst_solver_per_active                1400
% 11.44/2.00  --inst_solver_calls_frac                1.
% 11.44/2.00  --inst_passive_queue_type               priority_queues
% 11.44/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.44/2.00  --inst_passive_queues_freq              [25;2]
% 11.44/2.00  --inst_dismatching                      true
% 11.44/2.00  --inst_eager_unprocessed_to_passive     true
% 11.44/2.00  --inst_prop_sim_given                   true
% 11.44/2.00  --inst_prop_sim_new                     false
% 11.44/2.00  --inst_subs_new                         false
% 11.44/2.00  --inst_eq_res_simp                      false
% 11.44/2.00  --inst_subs_given                       false
% 11.44/2.00  --inst_orphan_elimination               true
% 11.44/2.00  --inst_learning_loop_flag               true
% 11.44/2.00  --inst_learning_start                   3000
% 11.44/2.00  --inst_learning_factor                  2
% 11.44/2.00  --inst_start_prop_sim_after_learn       3
% 11.44/2.00  --inst_sel_renew                        solver
% 11.44/2.00  --inst_lit_activity_flag                true
% 11.44/2.00  --inst_restr_to_given                   false
% 11.44/2.00  --inst_activity_threshold               500
% 11.44/2.00  --inst_out_proof                        true
% 11.44/2.00  
% 11.44/2.00  ------ Resolution Options
% 11.44/2.00  
% 11.44/2.00  --resolution_flag                       true
% 11.44/2.00  --res_lit_sel                           adaptive
% 11.44/2.00  --res_lit_sel_side                      none
% 11.44/2.00  --res_ordering                          kbo
% 11.44/2.00  --res_to_prop_solver                    active
% 11.44/2.00  --res_prop_simpl_new                    false
% 11.44/2.00  --res_prop_simpl_given                  true
% 11.44/2.00  --res_passive_queue_type                priority_queues
% 11.44/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.44/2.00  --res_passive_queues_freq               [15;5]
% 11.44/2.00  --res_forward_subs                      full
% 11.44/2.00  --res_backward_subs                     full
% 11.44/2.00  --res_forward_subs_resolution           true
% 11.44/2.00  --res_backward_subs_resolution          true
% 11.44/2.00  --res_orphan_elimination                true
% 11.44/2.00  --res_time_limit                        2.
% 11.44/2.00  --res_out_proof                         true
% 11.44/2.00  
% 11.44/2.00  ------ Superposition Options
% 11.44/2.00  
% 11.44/2.00  --superposition_flag                    true
% 11.44/2.00  --sup_passive_queue_type                priority_queues
% 11.44/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.44/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.44/2.00  --demod_completeness_check              fast
% 11.44/2.00  --demod_use_ground                      true
% 11.44/2.00  --sup_to_prop_solver                    passive
% 11.44/2.00  --sup_prop_simpl_new                    true
% 11.44/2.00  --sup_prop_simpl_given                  true
% 11.44/2.00  --sup_fun_splitting                     false
% 11.44/2.00  --sup_smt_interval                      50000
% 11.44/2.00  
% 11.44/2.00  ------ Superposition Simplification Setup
% 11.44/2.00  
% 11.44/2.00  --sup_indices_passive                   []
% 11.44/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.44/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.00  --sup_full_bw                           [BwDemod]
% 11.44/2.00  --sup_immed_triv                        [TrivRules]
% 11.44/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.44/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.00  --sup_immed_bw_main                     []
% 11.44/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.44/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.44/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.44/2.00  
% 11.44/2.00  ------ Combination Options
% 11.44/2.00  
% 11.44/2.00  --comb_res_mult                         3
% 11.44/2.00  --comb_sup_mult                         2
% 11.44/2.00  --comb_inst_mult                        10
% 11.44/2.00  
% 11.44/2.00  ------ Debug Options
% 11.44/2.00  
% 11.44/2.00  --dbg_backtrace                         false
% 11.44/2.00  --dbg_dump_prop_clauses                 false
% 11.44/2.00  --dbg_dump_prop_clauses_file            -
% 11.44/2.00  --dbg_out_stat                          false
% 11.44/2.00  ------ Parsing...
% 11.44/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.44/2.00  
% 11.44/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.44/2.00  
% 11.44/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.44/2.00  
% 11.44/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.44/2.00  ------ Proving...
% 11.44/2.00  ------ Problem Properties 
% 11.44/2.00  
% 11.44/2.00  
% 11.44/2.00  clauses                                 18
% 11.44/2.00  conjectures                             2
% 11.44/2.00  EPR                                     5
% 11.44/2.00  Horn                                    18
% 11.44/2.00  unary                                   11
% 11.44/2.00  binary                                  2
% 11.44/2.00  lits                                    31
% 11.44/2.00  lits eq                                 12
% 11.44/2.00  fd_pure                                 0
% 11.44/2.00  fd_pseudo                               0
% 11.44/2.00  fd_cond                                 0
% 11.44/2.00  fd_pseudo_cond                          1
% 11.44/2.00  AC symbols                              0
% 11.44/2.00  
% 11.44/2.00  ------ Schedule dynamic 5 is on 
% 11.44/2.00  
% 11.44/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.44/2.00  
% 11.44/2.00  
% 11.44/2.00  ------ 
% 11.44/2.00  Current options:
% 11.44/2.00  ------ 
% 11.44/2.00  
% 11.44/2.00  ------ Input Options
% 11.44/2.00  
% 11.44/2.00  --out_options                           all
% 11.44/2.00  --tptp_safe_out                         true
% 11.44/2.00  --problem_path                          ""
% 11.44/2.00  --include_path                          ""
% 11.44/2.00  --clausifier                            res/vclausify_rel
% 11.44/2.00  --clausifier_options                    --mode clausify
% 11.44/2.00  --stdin                                 false
% 11.44/2.00  --stats_out                             all
% 11.44/2.00  
% 11.44/2.00  ------ General Options
% 11.44/2.00  
% 11.44/2.00  --fof                                   false
% 11.44/2.00  --time_out_real                         305.
% 11.44/2.00  --time_out_virtual                      -1.
% 11.44/2.00  --symbol_type_check                     false
% 11.44/2.00  --clausify_out                          false
% 11.44/2.00  --sig_cnt_out                           false
% 11.44/2.00  --trig_cnt_out                          false
% 11.44/2.00  --trig_cnt_out_tolerance                1.
% 11.44/2.00  --trig_cnt_out_sk_spl                   false
% 11.44/2.00  --abstr_cl_out                          false
% 11.44/2.00  
% 11.44/2.00  ------ Global Options
% 11.44/2.00  
% 11.44/2.00  --schedule                              default
% 11.44/2.00  --add_important_lit                     false
% 11.44/2.00  --prop_solver_per_cl                    1000
% 11.44/2.00  --min_unsat_core                        false
% 11.44/2.00  --soft_assumptions                      false
% 11.44/2.00  --soft_lemma_size                       3
% 11.44/2.00  --prop_impl_unit_size                   0
% 11.44/2.00  --prop_impl_unit                        []
% 11.44/2.00  --share_sel_clauses                     true
% 11.44/2.00  --reset_solvers                         false
% 11.44/2.00  --bc_imp_inh                            [conj_cone]
% 11.44/2.00  --conj_cone_tolerance                   3.
% 11.44/2.00  --extra_neg_conj                        none
% 11.44/2.00  --large_theory_mode                     true
% 11.44/2.00  --prolific_symb_bound                   200
% 11.44/2.00  --lt_threshold                          2000
% 11.44/2.00  --clause_weak_htbl                      true
% 11.44/2.00  --gc_record_bc_elim                     false
% 11.44/2.00  
% 11.44/2.00  ------ Preprocessing Options
% 11.44/2.00  
% 11.44/2.00  --preprocessing_flag                    true
% 11.44/2.00  --time_out_prep_mult                    0.1
% 11.44/2.00  --splitting_mode                        input
% 11.44/2.00  --splitting_grd                         true
% 11.44/2.00  --splitting_cvd                         false
% 11.44/2.00  --splitting_cvd_svl                     false
% 11.44/2.00  --splitting_nvd                         32
% 11.44/2.00  --sub_typing                            true
% 11.44/2.00  --prep_gs_sim                           true
% 11.44/2.00  --prep_unflatten                        true
% 11.44/2.00  --prep_res_sim                          true
% 11.44/2.00  --prep_upred                            true
% 11.44/2.00  --prep_sem_filter                       exhaustive
% 11.44/2.00  --prep_sem_filter_out                   false
% 11.44/2.00  --pred_elim                             true
% 11.44/2.00  --res_sim_input                         true
% 11.44/2.00  --eq_ax_congr_red                       true
% 11.44/2.00  --pure_diseq_elim                       true
% 11.44/2.00  --brand_transform                       false
% 11.44/2.00  --non_eq_to_eq                          false
% 11.44/2.00  --prep_def_merge                        true
% 11.44/2.00  --prep_def_merge_prop_impl              false
% 11.44/2.00  --prep_def_merge_mbd                    true
% 11.44/2.00  --prep_def_merge_tr_red                 false
% 11.44/2.00  --prep_def_merge_tr_cl                  false
% 11.44/2.00  --smt_preprocessing                     true
% 11.44/2.00  --smt_ac_axioms                         fast
% 11.44/2.00  --preprocessed_out                      false
% 11.44/2.00  --preprocessed_stats                    false
% 11.44/2.00  
% 11.44/2.00  ------ Abstraction refinement Options
% 11.44/2.00  
% 11.44/2.00  --abstr_ref                             []
% 11.44/2.00  --abstr_ref_prep                        false
% 11.44/2.00  --abstr_ref_until_sat                   false
% 11.44/2.00  --abstr_ref_sig_restrict                funpre
% 11.44/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.44/2.00  --abstr_ref_under                       []
% 11.44/2.00  
% 11.44/2.00  ------ SAT Options
% 11.44/2.00  
% 11.44/2.00  --sat_mode                              false
% 11.44/2.00  --sat_fm_restart_options                ""
% 11.44/2.00  --sat_gr_def                            false
% 11.44/2.00  --sat_epr_types                         true
% 11.44/2.00  --sat_non_cyclic_types                  false
% 11.44/2.00  --sat_finite_models                     false
% 11.44/2.00  --sat_fm_lemmas                         false
% 11.44/2.00  --sat_fm_prep                           false
% 11.44/2.00  --sat_fm_uc_incr                        true
% 11.44/2.00  --sat_out_model                         small
% 11.44/2.00  --sat_out_clauses                       false
% 11.44/2.00  
% 11.44/2.00  ------ QBF Options
% 11.44/2.00  
% 11.44/2.00  --qbf_mode                              false
% 11.44/2.00  --qbf_elim_univ                         false
% 11.44/2.00  --qbf_dom_inst                          none
% 11.44/2.00  --qbf_dom_pre_inst                      false
% 11.44/2.00  --qbf_sk_in                             false
% 11.44/2.00  --qbf_pred_elim                         true
% 11.44/2.00  --qbf_split                             512
% 11.44/2.00  
% 11.44/2.00  ------ BMC1 Options
% 11.44/2.00  
% 11.44/2.00  --bmc1_incremental                      false
% 11.44/2.00  --bmc1_axioms                           reachable_all
% 11.44/2.00  --bmc1_min_bound                        0
% 11.44/2.00  --bmc1_max_bound                        -1
% 11.44/2.00  --bmc1_max_bound_default                -1
% 11.44/2.00  --bmc1_symbol_reachability              true
% 11.44/2.00  --bmc1_property_lemmas                  false
% 11.44/2.00  --bmc1_k_induction                      false
% 11.44/2.00  --bmc1_non_equiv_states                 false
% 11.44/2.00  --bmc1_deadlock                         false
% 11.44/2.00  --bmc1_ucm                              false
% 11.44/2.00  --bmc1_add_unsat_core                   none
% 11.44/2.00  --bmc1_unsat_core_children              false
% 11.44/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.44/2.00  --bmc1_out_stat                         full
% 11.44/2.00  --bmc1_ground_init                      false
% 11.44/2.00  --bmc1_pre_inst_next_state              false
% 11.44/2.00  --bmc1_pre_inst_state                   false
% 11.44/2.00  --bmc1_pre_inst_reach_state             false
% 11.44/2.00  --bmc1_out_unsat_core                   false
% 11.44/2.00  --bmc1_aig_witness_out                  false
% 11.44/2.00  --bmc1_verbose                          false
% 11.44/2.00  --bmc1_dump_clauses_tptp                false
% 11.44/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.44/2.00  --bmc1_dump_file                        -
% 11.44/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.44/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.44/2.00  --bmc1_ucm_extend_mode                  1
% 11.44/2.00  --bmc1_ucm_init_mode                    2
% 11.44/2.00  --bmc1_ucm_cone_mode                    none
% 11.44/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.44/2.00  --bmc1_ucm_relax_model                  4
% 11.44/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.44/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.44/2.00  --bmc1_ucm_layered_model                none
% 11.44/2.00  --bmc1_ucm_max_lemma_size               10
% 11.44/2.00  
% 11.44/2.00  ------ AIG Options
% 11.44/2.00  
% 11.44/2.00  --aig_mode                              false
% 11.44/2.00  
% 11.44/2.00  ------ Instantiation Options
% 11.44/2.00  
% 11.44/2.00  --instantiation_flag                    true
% 11.44/2.00  --inst_sos_flag                         false
% 11.44/2.00  --inst_sos_phase                        true
% 11.44/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.44/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.44/2.00  --inst_lit_sel_side                     none
% 11.44/2.00  --inst_solver_per_active                1400
% 11.44/2.00  --inst_solver_calls_frac                1.
% 11.44/2.00  --inst_passive_queue_type               priority_queues
% 11.44/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.44/2.00  --inst_passive_queues_freq              [25;2]
% 11.44/2.00  --inst_dismatching                      true
% 11.44/2.00  --inst_eager_unprocessed_to_passive     true
% 11.44/2.00  --inst_prop_sim_given                   true
% 11.44/2.00  --inst_prop_sim_new                     false
% 11.44/2.00  --inst_subs_new                         false
% 11.44/2.00  --inst_eq_res_simp                      false
% 11.44/2.00  --inst_subs_given                       false
% 11.44/2.00  --inst_orphan_elimination               true
% 11.44/2.00  --inst_learning_loop_flag               true
% 11.44/2.00  --inst_learning_start                   3000
% 11.44/2.00  --inst_learning_factor                  2
% 11.44/2.00  --inst_start_prop_sim_after_learn       3
% 11.44/2.00  --inst_sel_renew                        solver
% 11.44/2.00  --inst_lit_activity_flag                true
% 11.44/2.00  --inst_restr_to_given                   false
% 11.44/2.00  --inst_activity_threshold               500
% 11.44/2.00  --inst_out_proof                        true
% 11.44/2.00  
% 11.44/2.00  ------ Resolution Options
% 11.44/2.00  
% 11.44/2.00  --resolution_flag                       false
% 11.44/2.00  --res_lit_sel                           adaptive
% 11.44/2.00  --res_lit_sel_side                      none
% 11.44/2.00  --res_ordering                          kbo
% 11.44/2.00  --res_to_prop_solver                    active
% 11.44/2.00  --res_prop_simpl_new                    false
% 11.44/2.00  --res_prop_simpl_given                  true
% 11.44/2.00  --res_passive_queue_type                priority_queues
% 11.44/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.44/2.00  --res_passive_queues_freq               [15;5]
% 11.44/2.00  --res_forward_subs                      full
% 11.44/2.00  --res_backward_subs                     full
% 11.44/2.00  --res_forward_subs_resolution           true
% 11.44/2.00  --res_backward_subs_resolution          true
% 11.44/2.00  --res_orphan_elimination                true
% 11.44/2.00  --res_time_limit                        2.
% 11.44/2.00  --res_out_proof                         true
% 11.44/2.00  
% 11.44/2.00  ------ Superposition Options
% 11.44/2.00  
% 11.44/2.00  --superposition_flag                    true
% 11.44/2.00  --sup_passive_queue_type                priority_queues
% 11.44/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.44/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.44/2.00  --demod_completeness_check              fast
% 11.44/2.00  --demod_use_ground                      true
% 11.44/2.00  --sup_to_prop_solver                    passive
% 11.44/2.00  --sup_prop_simpl_new                    true
% 11.44/2.00  --sup_prop_simpl_given                  true
% 11.44/2.00  --sup_fun_splitting                     false
% 11.44/2.00  --sup_smt_interval                      50000
% 11.44/2.00  
% 11.44/2.00  ------ Superposition Simplification Setup
% 11.44/2.00  
% 11.44/2.00  --sup_indices_passive                   []
% 11.44/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.44/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.00  --sup_full_bw                           [BwDemod]
% 11.44/2.00  --sup_immed_triv                        [TrivRules]
% 11.44/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.44/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.00  --sup_immed_bw_main                     []
% 11.44/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.44/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.44/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.44/2.00  
% 11.44/2.00  ------ Combination Options
% 11.44/2.00  
% 11.44/2.00  --comb_res_mult                         3
% 11.44/2.00  --comb_sup_mult                         2
% 11.44/2.00  --comb_inst_mult                        10
% 11.44/2.00  
% 11.44/2.00  ------ Debug Options
% 11.44/2.00  
% 11.44/2.00  --dbg_backtrace                         false
% 11.44/2.00  --dbg_dump_prop_clauses                 false
% 11.44/2.00  --dbg_dump_prop_clauses_file            -
% 11.44/2.00  --dbg_out_stat                          false
% 11.44/2.00  
% 11.44/2.00  
% 11.44/2.00  
% 11.44/2.00  
% 11.44/2.00  ------ Proving...
% 11.44/2.00  
% 11.44/2.00  
% 11.44/2.00  % SZS status Theorem for theBenchmark.p
% 11.44/2.00  
% 11.44/2.00   Resolution empty clause
% 11.44/2.00  
% 11.44/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.44/2.00  
% 11.44/2.00  fof(f23,conjecture,(
% 11.44/2.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f24,negated_conjecture,(
% 11.44/2.00    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 11.44/2.00    inference(negated_conjecture,[],[f23])).
% 11.44/2.00  
% 11.44/2.00  fof(f33,plain,(
% 11.44/2.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 11.44/2.00    inference(ennf_transformation,[],[f24])).
% 11.44/2.00  
% 11.44/2.00  fof(f36,plain,(
% 11.44/2.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 11.44/2.00    introduced(choice_axiom,[])).
% 11.44/2.00  
% 11.44/2.00  fof(f37,plain,(
% 11.44/2.00    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 11.44/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f36])).
% 11.44/2.00  
% 11.44/2.00  fof(f64,plain,(
% 11.44/2.00    v1_relat_1(sK0)),
% 11.44/2.00    inference(cnf_transformation,[],[f37])).
% 11.44/2.00  
% 11.44/2.00  fof(f1,axiom,(
% 11.44/2.00    v1_xboole_0(k1_xboole_0)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f38,plain,(
% 11.44/2.00    v1_xboole_0(k1_xboole_0)),
% 11.44/2.00    inference(cnf_transformation,[],[f1])).
% 11.44/2.00  
% 11.44/2.00  fof(f16,axiom,(
% 11.44/2.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f26,plain,(
% 11.44/2.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 11.44/2.00    inference(ennf_transformation,[],[f16])).
% 11.44/2.00  
% 11.44/2.00  fof(f56,plain,(
% 11.44/2.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f26])).
% 11.44/2.00  
% 11.44/2.00  fof(f21,axiom,(
% 11.44/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f32,plain,(
% 11.44/2.00    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.44/2.00    inference(ennf_transformation,[],[f21])).
% 11.44/2.00  
% 11.44/2.00  fof(f61,plain,(
% 11.44/2.00    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f32])).
% 11.44/2.00  
% 11.44/2.00  fof(f17,axiom,(
% 11.44/2.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f27,plain,(
% 11.44/2.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 11.44/2.00    inference(ennf_transformation,[],[f17])).
% 11.44/2.00  
% 11.44/2.00  fof(f28,plain,(
% 11.44/2.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 11.44/2.00    inference(flattening,[],[f27])).
% 11.44/2.00  
% 11.44/2.00  fof(f57,plain,(
% 11.44/2.00    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f28])).
% 11.44/2.00  
% 11.44/2.00  fof(f18,axiom,(
% 11.44/2.00    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f29,plain,(
% 11.44/2.00    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 11.44/2.00    inference(ennf_transformation,[],[f18])).
% 11.44/2.00  
% 11.44/2.00  fof(f58,plain,(
% 11.44/2.00    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f29])).
% 11.44/2.00  
% 11.44/2.00  fof(f15,axiom,(
% 11.44/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f55,plain,(
% 11.44/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.44/2.00    inference(cnf_transformation,[],[f15])).
% 11.44/2.00  
% 11.44/2.00  fof(f8,axiom,(
% 11.44/2.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f47,plain,(
% 11.44/2.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f8])).
% 11.44/2.00  
% 11.44/2.00  fof(f9,axiom,(
% 11.44/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f48,plain,(
% 11.44/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f9])).
% 11.44/2.00  
% 11.44/2.00  fof(f10,axiom,(
% 11.44/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f49,plain,(
% 11.44/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f10])).
% 11.44/2.00  
% 11.44/2.00  fof(f11,axiom,(
% 11.44/2.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f50,plain,(
% 11.44/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f11])).
% 11.44/2.00  
% 11.44/2.00  fof(f12,axiom,(
% 11.44/2.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f51,plain,(
% 11.44/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f12])).
% 11.44/2.00  
% 11.44/2.00  fof(f13,axiom,(
% 11.44/2.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f52,plain,(
% 11.44/2.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f13])).
% 11.44/2.00  
% 11.44/2.00  fof(f66,plain,(
% 11.44/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.44/2.00    inference(definition_unfolding,[],[f51,f52])).
% 11.44/2.00  
% 11.44/2.00  fof(f67,plain,(
% 11.44/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.44/2.00    inference(definition_unfolding,[],[f50,f66])).
% 11.44/2.00  
% 11.44/2.00  fof(f68,plain,(
% 11.44/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.44/2.00    inference(definition_unfolding,[],[f49,f67])).
% 11.44/2.00  
% 11.44/2.00  fof(f69,plain,(
% 11.44/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.44/2.00    inference(definition_unfolding,[],[f48,f68])).
% 11.44/2.00  
% 11.44/2.00  fof(f70,plain,(
% 11.44/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.44/2.00    inference(definition_unfolding,[],[f47,f69])).
% 11.44/2.00  
% 11.44/2.00  fof(f71,plain,(
% 11.44/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.44/2.00    inference(definition_unfolding,[],[f55,f70])).
% 11.44/2.00  
% 11.44/2.00  fof(f77,plain,(
% 11.44/2.00    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 11.44/2.00    inference(definition_unfolding,[],[f58,f71])).
% 11.44/2.00  
% 11.44/2.00  fof(f20,axiom,(
% 11.44/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f31,plain,(
% 11.44/2.00    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.44/2.00    inference(ennf_transformation,[],[f20])).
% 11.44/2.00  
% 11.44/2.00  fof(f60,plain,(
% 11.44/2.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f31])).
% 11.44/2.00  
% 11.44/2.00  fof(f22,axiom,(
% 11.44/2.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f63,plain,(
% 11.44/2.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 11.44/2.00    inference(cnf_transformation,[],[f22])).
% 11.44/2.00  
% 11.44/2.00  fof(f3,axiom,(
% 11.44/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f34,plain,(
% 11.44/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.44/2.00    inference(nnf_transformation,[],[f3])).
% 11.44/2.00  
% 11.44/2.00  fof(f35,plain,(
% 11.44/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.44/2.00    inference(flattening,[],[f34])).
% 11.44/2.00  
% 11.44/2.00  fof(f42,plain,(
% 11.44/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f35])).
% 11.44/2.00  
% 11.44/2.00  fof(f6,axiom,(
% 11.44/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f45,plain,(
% 11.44/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f6])).
% 11.44/2.00  
% 11.44/2.00  fof(f5,axiom,(
% 11.44/2.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f44,plain,(
% 11.44/2.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f5])).
% 11.44/2.00  
% 11.44/2.00  fof(f74,plain,(
% 11.44/2.00    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 11.44/2.00    inference(definition_unfolding,[],[f44,f71])).
% 11.44/2.00  
% 11.44/2.00  fof(f2,axiom,(
% 11.44/2.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f25,plain,(
% 11.44/2.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.44/2.00    inference(rectify,[],[f2])).
% 11.44/2.00  
% 11.44/2.00  fof(f39,plain,(
% 11.44/2.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.44/2.00    inference(cnf_transformation,[],[f25])).
% 11.44/2.00  
% 11.44/2.00  fof(f73,plain,(
% 11.44/2.00    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 11.44/2.00    inference(definition_unfolding,[],[f39,f71])).
% 11.44/2.00  
% 11.44/2.00  fof(f14,axiom,(
% 11.44/2.00    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f54,plain,(
% 11.44/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))) )),
% 11.44/2.00    inference(cnf_transformation,[],[f14])).
% 11.44/2.00  
% 11.44/2.00  fof(f4,axiom,(
% 11.44/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f43,plain,(
% 11.44/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.44/2.00    inference(cnf_transformation,[],[f4])).
% 11.44/2.00  
% 11.44/2.00  fof(f72,plain,(
% 11.44/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.44/2.00    inference(definition_unfolding,[],[f43,f71])).
% 11.44/2.00  
% 11.44/2.00  fof(f75,plain,(
% 11.44/2.00    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 11.44/2.00    inference(definition_unfolding,[],[f54,f72,f72])).
% 11.44/2.00  
% 11.44/2.00  fof(f7,axiom,(
% 11.44/2.00    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f46,plain,(
% 11.44/2.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f7])).
% 11.44/2.00  
% 11.44/2.00  fof(f19,axiom,(
% 11.44/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 11.44/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.44/2.00  
% 11.44/2.00  fof(f30,plain,(
% 11.44/2.00    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.44/2.00    inference(ennf_transformation,[],[f19])).
% 11.44/2.00  
% 11.44/2.00  fof(f59,plain,(
% 11.44/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f30])).
% 11.44/2.00  
% 11.44/2.00  fof(f62,plain,(
% 11.44/2.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.44/2.00    inference(cnf_transformation,[],[f22])).
% 11.44/2.00  
% 11.44/2.00  fof(f53,plain,(
% 11.44/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) )),
% 11.44/2.00    inference(cnf_transformation,[],[f14])).
% 11.44/2.00  
% 11.44/2.00  fof(f76,plain,(
% 11.44/2.00    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2)) )),
% 11.44/2.00    inference(definition_unfolding,[],[f53,f72,f72])).
% 11.44/2.00  
% 11.44/2.00  fof(f65,plain,(
% 11.44/2.00    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 11.44/2.00    inference(cnf_transformation,[],[f37])).
% 11.44/2.00  
% 11.44/2.00  cnf(c_19,negated_conjecture,
% 11.44/2.00      ( v1_relat_1(sK0) ),
% 11.44/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_421,plain,
% 11.44/2.00      ( v1_relat_1(sK0) = iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_0,plain,
% 11.44/2.00      ( v1_xboole_0(k1_xboole_0) ),
% 11.44/2.00      inference(cnf_transformation,[],[f38]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_10,plain,
% 11.44/2.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 11.44/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_147,plain,
% 11.44/2.00      ( v1_relat_1(X0) | k1_xboole_0 != X0 ),
% 11.44/2.00      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_148,plain,
% 11.44/2.00      ( v1_relat_1(k1_xboole_0) ),
% 11.44/2.00      inference(unflattening,[status(thm)],[c_147]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_420,plain,
% 11.44/2.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_15,plain,
% 11.44/2.00      ( ~ v1_relat_1(X0)
% 11.44/2.00      | ~ v1_relat_1(X1)
% 11.44/2.00      | ~ v1_relat_1(X2)
% 11.44/2.00      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 11.44/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_422,plain,
% 11.44/2.00      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 11.44/2.00      | v1_relat_1(X1) != iProver_top
% 11.44/2.00      | v1_relat_1(X0) != iProver_top
% 11.44/2.00      | v1_relat_1(X2) != iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_638,plain,
% 11.44/2.00      ( k5_relat_1(sK0,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK0,X0),X1)
% 11.44/2.00      | v1_relat_1(X0) != iProver_top
% 11.44/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_421,c_422]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_887,plain,
% 11.44/2.00      ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X0) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,X0))
% 11.44/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_420,c_638]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1016,plain,
% 11.44/2.00      ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0) ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_421,c_887]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_11,plain,
% 11.44/2.00      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 11.44/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_426,plain,
% 11.44/2.00      ( v1_relat_1(X0) != iProver_top
% 11.44/2.00      | v1_relat_1(X1) != iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2377,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 11.44/2.00      | v1_relat_1(sK0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_1016,c_426]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_20,plain,
% 11.44/2.00      ( v1_relat_1(sK0) = iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_36,plain,
% 11.44/2.00      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_38,plain,
% 11.44/2.00      ( v1_relat_1(k1_xboole_0) = iProver_top
% 11.44/2.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(instantiation,[status(thm)],[c_36]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_51,plain,
% 11.44/2.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1088,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 11.44/2.00      | ~ v1_relat_1(sK0)
% 11.44/2.00      | ~ v1_relat_1(k1_xboole_0) ),
% 11.44/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1089,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 11.44/2.00      | v1_relat_1(sK0) != iProver_top
% 11.44/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_1088]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2888,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
% 11.44/2.00      inference(global_propositional_subsumption,
% 11.44/2.00                [status(thm)],
% 11.44/2.00                [c_2377,c_20,c_38,c_51,c_1089]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_12,plain,
% 11.44/2.00      ( ~ v1_relat_1(X0)
% 11.44/2.00      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 11.44/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_425,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 11.44/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2893,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)))))) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_2888,c_425]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_639,plain,
% 11.44/2.00      ( k5_relat_1(k1_xboole_0,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k1_xboole_0,X0),X1)
% 11.44/2.00      | v1_relat_1(X0) != iProver_top
% 11.44/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_420,c_422]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_3586,plain,
% 11.44/2.00      ( k5_relat_1(k5_relat_1(k1_xboole_0,sK0),X0) = k5_relat_1(k1_xboole_0,k5_relat_1(sK0,X0))
% 11.44/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_421,c_639]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_4611,plain,
% 11.44/2.00      ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k5_relat_1(X0,X1))) = k5_relat_1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(X0,X1))
% 11.44/2.00      | v1_relat_1(X1) != iProver_top
% 11.44/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_426,c_3586]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_6512,plain,
% 11.44/2.00      ( k5_relat_1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k5_relat_1(sK0,X0)))
% 11.44/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_421,c_4611]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_6572,plain,
% 11.44/2.00      ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(sK0,k1_xboole_0)) ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_420,c_6512]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_7372,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)))) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_6572,c_426]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_15683,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)))) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 11.44/2.00      inference(global_propositional_subsumption,
% 11.44/2.00                [status(thm)],
% 11.44/2.00                [c_7372,c_20,c_38,c_51,c_1089]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_886,plain,
% 11.44/2.00      ( k5_relat_1(k5_relat_1(sK0,sK0),X0) = k5_relat_1(sK0,k5_relat_1(sK0,X0))
% 11.44/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_421,c_638]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_956,plain,
% 11.44/2.00      ( k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k5_relat_1(sK0,sK0),k1_xboole_0) ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_420,c_886]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2375,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top
% 11.44/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_956,c_426]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_8621,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 11.44/2.00      inference(global_propositional_subsumption,
% 11.44/2.00                [status(thm)],
% 11.44/2.00                [c_2375,c_38,c_51]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_8622,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
% 11.44/2.00      inference(renaming,[status(thm)],[c_8621]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_8634,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)))))) = k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_8622,c_425]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_14,plain,
% 11.44/2.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 11.44/2.00      | ~ v1_relat_1(X1)
% 11.44/2.00      | ~ v1_relat_1(X0) ),
% 11.44/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_423,plain,
% 11.44/2.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 11.44/2.00      | v1_relat_1(X0) != iProver_top
% 11.44/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1184,plain,
% 11.44/2.00      ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k1_xboole_0)) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top
% 11.44/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_956,c_423]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_16,plain,
% 11.44/2.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.44/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1209,plain,
% 11.44/2.00      ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top
% 11.44/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_1184,c_16]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2058,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top
% 11.44/2.00      | r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) = iProver_top ),
% 11.44/2.00      inference(global_propositional_subsumption,
% 11.44/2.00                [status(thm)],
% 11.44/2.00                [c_1209,c_38,c_51]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2059,plain,
% 11.44/2.00      ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
% 11.44/2.00      inference(renaming,[status(thm)],[c_2058]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2,plain,
% 11.44/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.44/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_429,plain,
% 11.44/2.00      ( X0 = X1
% 11.44/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.44/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2064,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 11.44/2.00      | r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_2059,c_429]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_6,plain,
% 11.44/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 11.44/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_427,plain,
% 11.44/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2135,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
% 11.44/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_2064,c_427]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2382,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 11.44/2.00      | v1_relat_1(sK0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_426,c_2135]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_7219,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 11.44/2.00      inference(global_propositional_subsumption,[status(thm)],[c_2382,c_20]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_8663,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0))) = k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_8634,c_7219]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_5,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.44/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 11.44/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_8,plain,
% 11.44/2.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 11.44/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_770,plain,
% 11.44/2.00      ( k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_7,plain,
% 11.44/2.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.44/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_771,plain,
% 11.44/2.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.44/2.00      inference(demodulation,[status(thm)],[c_770,c_1,c_7]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_8664,plain,
% 11.44/2.00      ( k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,sK0)) != iProver_top ),
% 11.44/2.00      inference(demodulation,[status(thm)],[c_8663,c_5,c_771]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_8911,plain,
% 11.44/2.00      ( k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
% 11.44/2.00      | v1_relat_1(sK0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_426,c_8664]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_11041,plain,
% 11.44/2.00      ( k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 11.44/2.00      inference(global_propositional_subsumption,[status(thm)],[c_8911,c_20]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_15687,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_15683,c_11041]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_33,plain,
% 11.44/2.00      ( v1_relat_1(X0) != iProver_top
% 11.44/2.00      | v1_relat_1(X1) != iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_35,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 11.44/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(instantiation,[status(thm)],[c_33]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_15691,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 11.44/2.00      inference(global_propositional_subsumption,
% 11.44/2.00                [status(thm)],
% 11.44/2.00                [c_15687,c_35,c_38,c_51]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_15709,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))))) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_15691,c_425]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1017,plain,
% 11.44/2.00      ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_420,c_887]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2374,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 11.44/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_1017,c_426]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_7238,plain,
% 11.44/2.00      ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.44/2.00      inference(global_propositional_subsumption,
% 11.44/2.00                [status(thm)],
% 11.44/2.00                [c_2374,c_20,c_38,c_51,c_1089]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_7250,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))),k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)))))) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_7238,c_425]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1183,plain,
% 11.44/2.00      ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))),k2_relat_1(k1_xboole_0)) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 11.44/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_1017,c_423]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1216,plain,
% 11.44/2.00      ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 11.44/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_1183,c_16]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2067,plain,
% 11.44/2.00      ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0) = iProver_top ),
% 11.44/2.00      inference(global_propositional_subsumption,
% 11.44/2.00                [status(thm)],
% 11.44/2.00                [c_1216,c_20,c_38,c_51,c_1089]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2072,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = k1_xboole_0
% 11.44/2.00      | r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)))) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_2067,c_429]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2140,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
% 11.44/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_2072,c_427]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_7270,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0))) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_7250,c_2140]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_7271,plain,
% 11.44/2.00      ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 11.44/2.00      inference(demodulation,[status(thm)],[c_7270,c_5,c_771]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1544,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 11.44/2.00      | r1_tarski(k2_relat_1(X1),k2_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 11.44/2.00      | v1_relat_1(X0) != iProver_top
% 11.44/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_423,c_429]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_10305,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
% 11.44/2.00      | r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k2_relat_1(k1_xboole_0)) != iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 11.44/2.00      | v1_relat_1(sK0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_7271,c_1544]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_10435,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 11.44/2.00      | r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) != iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 11.44/2.00      | v1_relat_1(sK0) != iProver_top ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_10305,c_16,c_7271]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1187,plain,
% 11.44/2.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 11.44/2.00      | v1_relat_1(X0) != iProver_top
% 11.44/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_16,c_423]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2588,plain,
% 11.44/2.00      ( v1_relat_1(X0) != iProver_top
% 11.44/2.00      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 11.44/2.00      inference(global_propositional_subsumption,
% 11.44/2.00                [status(thm)],
% 11.44/2.00                [c_1187,c_38,c_51]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2589,plain,
% 11.44/2.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 11.44/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.00      inference(renaming,[status(thm)],[c_2588]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_1543,plain,
% 11.44/2.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_427,c_429]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_7026,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 11.44/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_2589,c_1543]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_7038,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 11.44/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.44/2.00      inference(instantiation,[status(thm)],[c_7026]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_10478,plain,
% 11.44/2.00      ( k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 11.44/2.00      inference(global_propositional_subsumption,
% 11.44/2.00                [status(thm)],
% 11.44/2.00                [c_10435,c_38,c_51,c_7038]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_15731,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_15709,c_10478]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_15732,plain,
% 11.44/2.00      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.44/2.00      inference(demodulation,[status(thm)],[c_15731,c_5,c_771]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_17417,plain,
% 11.44/2.00      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 11.44/2.00      inference(demodulation,[status(thm)],[c_15732,c_7271]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_19480,plain,
% 11.44/2.00      ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k1_xboole_0,sK0) ),
% 11.44/2.00      inference(demodulation,[status(thm)],[c_17417,c_1016]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_13,plain,
% 11.44/2.00      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 11.44/2.00      | ~ v1_relat_1(X1)
% 11.44/2.00      | ~ v1_relat_1(X0) ),
% 11.44/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_424,plain,
% 11.44/2.00      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 11.44/2.00      | v1_relat_1(X0) != iProver_top
% 11.44/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.44/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_2319,plain,
% 11.44/2.00      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k1_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 11.44/2.00      | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 11.44/2.00      | v1_relat_1(sK0) != iProver_top ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_1016,c_424]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_3359,plain,
% 11.44/2.00      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k1_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 11.44/2.00      inference(global_propositional_subsumption,
% 11.44/2.00                [status(thm)],
% 11.44/2.00                [c_2319,c_20,c_38,c_51,c_1089]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_19479,plain,
% 11.44/2.00      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k1_relat_1(k1_xboole_0)) = iProver_top ),
% 11.44/2.00      inference(demodulation,[status(thm)],[c_17417,c_3359]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_19492,plain,
% 11.44/2.00      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0)) = iProver_top ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_19479,c_19480]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_17,plain,
% 11.44/2.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.44/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_19494,plain,
% 11.44/2.00      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) = iProver_top ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_19492,c_17]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_19543,plain,
% 11.44/2.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_19494,c_1543]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_24097,plain,
% 11.44/2.00      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_2893,c_19480,c_19543]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_9,plain,
% 11.44/2.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
% 11.44/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_871,plain,
% 11.44/2.00      ( k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
% 11.44/2.00      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_878,plain,
% 11.44/2.00      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k1_xboole_0,X1) ),
% 11.44/2.00      inference(light_normalisation,[status(thm)],[c_871,c_1,c_7]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_879,plain,
% 11.44/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.44/2.00      inference(demodulation,[status(thm)],[c_878,c_7]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_24098,plain,
% 11.44/2.00      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 11.44/2.00      inference(demodulation,[status(thm)],[c_24097,c_5,c_879]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_18,negated_conjecture,
% 11.44/2.00      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 11.44/2.00      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 11.44/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_19482,plain,
% 11.44/2.00      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
% 11.44/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.44/2.00      inference(demodulation,[status(thm)],[c_17417,c_18]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_19483,plain,
% 11.44/2.00      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
% 11.44/2.00      inference(equality_resolution_simp,[status(thm)],[c_19482]) ).
% 11.44/2.00  
% 11.44/2.00  cnf(c_24100,plain,
% 11.44/2.00      ( $false ),
% 11.44/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_24098,c_19483]) ).
% 11.44/2.00  
% 11.44/2.00  
% 11.44/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.44/2.00  
% 11.44/2.00  ------                               Statistics
% 11.44/2.00  
% 11.44/2.00  ------ General
% 11.44/2.00  
% 11.44/2.00  abstr_ref_over_cycles:                  0
% 11.44/2.00  abstr_ref_under_cycles:                 0
% 11.44/2.00  gc_basic_clause_elim:                   0
% 11.44/2.00  forced_gc_time:                         0
% 11.44/2.00  parsing_time:                           0.008
% 11.44/2.00  unif_index_cands_time:                  0.
% 11.44/2.00  unif_index_add_time:                    0.
% 11.44/2.00  orderings_time:                         0.
% 11.44/2.00  out_proof_time:                         0.014
% 11.44/2.00  total_time:                             1.1
% 11.44/2.00  num_of_symbols:                         43
% 11.44/2.00  num_of_terms:                           16080
% 11.44/2.00  
% 11.44/2.00  ------ Preprocessing
% 11.44/2.00  
% 11.44/2.00  num_of_splits:                          0
% 11.44/2.00  num_of_split_atoms:                     0
% 11.44/2.00  num_of_reused_defs:                     0
% 11.44/2.00  num_eq_ax_congr_red:                    0
% 11.44/2.00  num_of_sem_filtered_clauses:            1
% 11.44/2.00  num_of_subtypes:                        0
% 11.44/2.00  monotx_restored_types:                  0
% 11.44/2.00  sat_num_of_epr_types:                   0
% 11.44/2.00  sat_num_of_non_cyclic_types:            0
% 11.44/2.00  sat_guarded_non_collapsed_types:        0
% 11.44/2.00  num_pure_diseq_elim:                    0
% 11.44/2.00  simp_replaced_by:                       0
% 11.44/2.00  res_preprocessed:                       96
% 11.44/2.00  prep_upred:                             0
% 11.44/2.00  prep_unflattend:                        1
% 11.44/2.00  smt_new_axioms:                         0
% 11.44/2.00  pred_elim_cands:                        2
% 11.44/2.00  pred_elim:                              1
% 11.44/2.00  pred_elim_cl:                           1
% 11.44/2.00  pred_elim_cycles:                       3
% 11.44/2.00  merged_defs:                            0
% 11.44/2.00  merged_defs_ncl:                        0
% 11.44/2.00  bin_hyper_res:                          0
% 11.44/2.00  prep_cycles:                            4
% 11.44/2.00  pred_elim_time:                         0.
% 11.44/2.00  splitting_time:                         0.
% 11.44/2.00  sem_filter_time:                        0.
% 11.44/2.00  monotx_time:                            0.
% 11.44/2.00  subtype_inf_time:                       0.
% 11.44/2.00  
% 11.44/2.00  ------ Problem properties
% 11.44/2.00  
% 11.44/2.00  clauses:                                18
% 11.44/2.00  conjectures:                            2
% 11.44/2.00  epr:                                    5
% 11.44/2.00  horn:                                   18
% 11.44/2.00  ground:                                 5
% 11.44/2.00  unary:                                  11
% 11.44/2.00  binary:                                 2
% 11.44/2.00  lits:                                   31
% 11.44/2.00  lits_eq:                                12
% 11.44/2.00  fd_pure:                                0
% 11.44/2.00  fd_pseudo:                              0
% 11.44/2.00  fd_cond:                                0
% 11.44/2.00  fd_pseudo_cond:                         1
% 11.44/2.00  ac_symbols:                             0
% 11.44/2.00  
% 11.44/2.00  ------ Propositional Solver
% 11.44/2.00  
% 11.44/2.00  prop_solver_calls:                      33
% 11.44/2.00  prop_fast_solver_calls:                 929
% 11.44/2.00  smt_solver_calls:                       0
% 11.44/2.00  smt_fast_solver_calls:                  0
% 11.44/2.00  prop_num_of_clauses:                    7520
% 11.44/2.00  prop_preprocess_simplified:             17051
% 11.44/2.00  prop_fo_subsumed:                       70
% 11.44/2.00  prop_solver_time:                       0.
% 11.44/2.00  smt_solver_time:                        0.
% 11.44/2.00  smt_fast_solver_time:                   0.
% 11.44/2.00  prop_fast_solver_time:                  0.
% 11.44/2.00  prop_unsat_core_time:                   0.
% 11.44/2.00  
% 11.44/2.00  ------ QBF
% 11.44/2.00  
% 11.44/2.00  qbf_q_res:                              0
% 11.44/2.00  qbf_num_tautologies:                    0
% 11.44/2.00  qbf_prep_cycles:                        0
% 11.44/2.00  
% 11.44/2.00  ------ BMC1
% 11.44/2.00  
% 11.44/2.00  bmc1_current_bound:                     -1
% 11.44/2.00  bmc1_last_solved_bound:                 -1
% 11.44/2.00  bmc1_unsat_core_size:                   -1
% 11.44/2.00  bmc1_unsat_core_parents_size:           -1
% 11.44/2.00  bmc1_merge_next_fun:                    0
% 11.44/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.44/2.00  
% 11.44/2.00  ------ Instantiation
% 11.44/2.00  
% 11.44/2.00  inst_num_of_clauses:                    2518
% 11.44/2.00  inst_num_in_passive:                    1607
% 11.44/2.00  inst_num_in_active:                     600
% 11.44/2.00  inst_num_in_unprocessed:                311
% 11.44/2.00  inst_num_of_loops:                      920
% 11.44/2.00  inst_num_of_learning_restarts:          0
% 11.44/2.00  inst_num_moves_active_passive:          315
% 11.44/2.00  inst_lit_activity:                      0
% 11.44/2.00  inst_lit_activity_moves:                1
% 11.44/2.00  inst_num_tautologies:                   0
% 11.44/2.00  inst_num_prop_implied:                  0
% 11.44/2.00  inst_num_existing_simplified:           0
% 11.44/2.00  inst_num_eq_res_simplified:             0
% 11.44/2.00  inst_num_child_elim:                    0
% 11.44/2.00  inst_num_of_dismatching_blockings:      1501
% 11.44/2.00  inst_num_of_non_proper_insts:           3058
% 11.44/2.00  inst_num_of_duplicates:                 0
% 11.44/2.00  inst_inst_num_from_inst_to_res:         0
% 11.44/2.00  inst_dismatching_checking_time:         0.
% 11.44/2.00  
% 11.44/2.00  ------ Resolution
% 11.44/2.00  
% 11.44/2.00  res_num_of_clauses:                     0
% 11.44/2.00  res_num_in_passive:                     0
% 11.44/2.00  res_num_in_active:                      0
% 11.44/2.00  res_num_of_loops:                       100
% 11.44/2.00  res_forward_subset_subsumed:            688
% 11.44/2.00  res_backward_subset_subsumed:           0
% 11.44/2.00  res_forward_subsumed:                   0
% 11.44/2.00  res_backward_subsumed:                  0
% 11.44/2.00  res_forward_subsumption_resolution:     0
% 11.44/2.00  res_backward_subsumption_resolution:    0
% 11.44/2.00  res_clause_to_clause_subsumption:       2791
% 11.44/2.00  res_orphan_elimination:                 0
% 11.44/2.00  res_tautology_del:                      260
% 11.44/2.00  res_num_eq_res_simplified:              0
% 11.44/2.00  res_num_sel_changes:                    0
% 11.44/2.00  res_moves_from_active_to_pass:          0
% 11.44/2.00  
% 11.44/2.00  ------ Superposition
% 11.44/2.00  
% 11.44/2.00  sup_time_total:                         0.
% 11.44/2.00  sup_time_generating:                    0.
% 11.44/2.00  sup_time_sim_full:                      0.
% 11.44/2.00  sup_time_sim_immed:                     0.
% 11.44/2.00  
% 11.44/2.00  sup_num_of_clauses:                     629
% 11.44/2.00  sup_num_in_active:                      114
% 11.44/2.00  sup_num_in_passive:                     515
% 11.44/2.00  sup_num_of_loops:                       182
% 11.44/2.00  sup_fw_superposition:                   888
% 11.44/2.00  sup_bw_superposition:                   511
% 11.44/2.00  sup_immediate_simplified:               308
% 11.44/2.00  sup_given_eliminated:                   3
% 11.44/2.00  comparisons_done:                       0
% 11.44/2.00  comparisons_avoided:                    0
% 11.44/2.00  
% 11.44/2.00  ------ Simplifications
% 11.44/2.00  
% 11.44/2.00  
% 11.44/2.00  sim_fw_subset_subsumed:                 14
% 11.44/2.00  sim_bw_subset_subsumed:                 11
% 11.44/2.00  sim_fw_subsumed:                        46
% 11.44/2.00  sim_bw_subsumed:                        0
% 11.44/2.00  sim_fw_subsumption_res:                 7
% 11.44/2.00  sim_bw_subsumption_res:                 0
% 11.44/2.00  sim_tautology_del:                      11
% 11.44/2.00  sim_eq_tautology_del:                   71
% 11.44/2.00  sim_eq_res_simp:                        1
% 11.44/2.00  sim_fw_demodulated:                     112
% 11.44/2.00  sim_bw_demodulated:                     74
% 11.44/2.00  sim_light_normalised:                   246
% 11.44/2.00  sim_joinable_taut:                      0
% 11.44/2.00  sim_joinable_simp:                      0
% 11.44/2.00  sim_ac_normalised:                      0
% 11.44/2.00  sim_smt_subsumption:                    0
% 11.44/2.00  
%------------------------------------------------------------------------------
