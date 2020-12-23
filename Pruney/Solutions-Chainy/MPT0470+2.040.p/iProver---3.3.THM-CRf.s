%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:01 EST 2020

% Result     : Theorem 27.47s
% Output     : CNFRefutation 27.47s
% Verified   : 
% Statistics : Number of formulae       :  172 (2236 expanded)
%              Number of clauses        :   96 ( 528 expanded)
%              Number of leaves         :   24 ( 590 expanded)
%              Depth                    :   27
%              Number of atoms          :  334 (3550 expanded)
%              Number of equality atoms :  233 (2309 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f34,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f37])).

fof(f65,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f58,plain,(
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

fof(f59,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f70])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f78,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f45,f72])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f44,f72])).

fof(f77,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) ),
    inference(definition_unfolding,[],[f54,f73,f73])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f55,f73,f73])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f72])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f66,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_10,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_147,plain,
    ( v1_relat_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_148,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_409,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_410,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_415,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_414,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2490,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_414])).

cnf(c_52715,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0))))) = k5_relat_1(sK0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_2490])).

cnf(c_53883,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_409,c_52715])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_411,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_756,plain,
    ( k5_relat_1(sK0,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK0,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_411])).

cnf(c_942,plain,
    ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X0) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_756])).

cnf(c_1194,plain,
    ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0) ),
    inference(superposition,[status(thm)],[c_410,c_942])).

cnf(c_1908,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_415])).

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

cnf(c_790,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_791,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_2015,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1908,c_20,c_38,c_51,c_791])).

cnf(c_16,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_413,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2301,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_413])).

cnf(c_2476,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2301,c_38,c_51])).

cnf(c_2477,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2476])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_416,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_418,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1787,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_416,c_418])).

cnf(c_2483,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_1787])).

cnf(c_50242,plain,
    ( k2_relat_1(k5_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2015,c_2483])).

cnf(c_1912,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),k5_relat_1(X2,X3)) = k5_relat_1(k5_relat_1(k5_relat_1(X0,X1),X2),X3)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_411])).

cnf(c_17393,plain,
    ( k5_relat_1(k5_relat_1(k5_relat_1(sK0,X0),X1),X2) = k5_relat_1(k5_relat_1(sK0,X0),k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_1912])).

cnf(c_18349,plain,
    ( k5_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X0),X1) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_17393])).

cnf(c_25428,plain,
    ( k5_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0),X0) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_18349])).

cnf(c_25446,plain,
    ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,X0)) = k5_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25428,c_1194])).

cnf(c_25495,plain,
    ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_409,c_25446])).

cnf(c_1909,plain,
    ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(X0,X1))) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_942])).

cnf(c_12666,plain,
    ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,X0)) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(sK0,X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_1909])).

cnf(c_13136,plain,
    ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_409,c_12666])).

cnf(c_757,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k1_xboole_0,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_411])).

cnf(c_2896,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK0),X0) = k5_relat_1(k1_xboole_0,k5_relat_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_757])).

cnf(c_3195,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_409,c_2896])).

cnf(c_3358,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3195,c_415])).

cnf(c_10853,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3358,c_38,c_51])).

cnf(c_10854,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10853])).

cnf(c_10869,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)))))) = k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10854,c_414])).

cnf(c_14,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_412,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1461,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_412])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1463,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1461,c_17])).

cnf(c_2914,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1463,c_38,c_51])).

cnf(c_2915,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2914])).

cnf(c_2918,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_416,c_2915])).

cnf(c_7015,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(X0,X1))) = k1_xboole_0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_2918])).

cnf(c_8433,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,X0))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_7015])).

cnf(c_8656,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_409,c_8433])).

cnf(c_10876,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)))))) = k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10869,c_8656])).

cnf(c_5,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_9,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_935,plain,
    ( k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_936,plain,
    ( k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(light_normalisation,[status(thm)],[c_935,c_1,c_7])).

cnf(c_869,plain,
    ( k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_870,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_869,c_1,c_7])).

cnf(c_937,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_936,c_1,c_7,c_870])).

cnf(c_10877,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10876,c_5,c_937])).

cnf(c_10914,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_10877])).

cnf(c_12950,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10914,c_20,c_38,c_51])).

cnf(c_13145,plain,
    ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_13136,c_12950])).

cnf(c_25510,plain,
    ( k5_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_25495,c_13145])).

cnf(c_50254,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_50242,c_25510])).

cnf(c_53902,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_53883,c_50254])).

cnf(c_53903,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_53902,c_5,c_870])).

cnf(c_54533,plain,
    ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(demodulation,[status(thm)],[c_53903,c_1194])).

cnf(c_2493,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)))))) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[status(thm)],[c_2015,c_414])).

cnf(c_54808,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(demodulation,[status(thm)],[c_54533,c_2493])).

cnf(c_7016,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_410,c_2918])).

cnf(c_54865,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_54808,c_7016])).

cnf(c_54866,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_54865,c_5,c_937])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_54536,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_53903,c_18])).

cnf(c_54537,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_54536])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54866,c_54537])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:30:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.47/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.47/3.99  
% 27.47/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.47/3.99  
% 27.47/3.99  ------  iProver source info
% 27.47/3.99  
% 27.47/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.47/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.47/3.99  git: non_committed_changes: false
% 27.47/3.99  git: last_make_outside_of_git: false
% 27.47/3.99  
% 27.47/3.99  ------ 
% 27.47/3.99  
% 27.47/3.99  ------ Input Options
% 27.47/3.99  
% 27.47/3.99  --out_options                           all
% 27.47/3.99  --tptp_safe_out                         true
% 27.47/3.99  --problem_path                          ""
% 27.47/3.99  --include_path                          ""
% 27.47/3.99  --clausifier                            res/vclausify_rel
% 27.47/3.99  --clausifier_options                    ""
% 27.47/3.99  --stdin                                 false
% 27.47/3.99  --stats_out                             all
% 27.47/3.99  
% 27.47/3.99  ------ General Options
% 27.47/3.99  
% 27.47/3.99  --fof                                   false
% 27.47/3.99  --time_out_real                         305.
% 27.47/3.99  --time_out_virtual                      -1.
% 27.47/3.99  --symbol_type_check                     false
% 27.47/3.99  --clausify_out                          false
% 27.47/3.99  --sig_cnt_out                           false
% 27.47/3.99  --trig_cnt_out                          false
% 27.47/3.99  --trig_cnt_out_tolerance                1.
% 27.47/3.99  --trig_cnt_out_sk_spl                   false
% 27.47/3.99  --abstr_cl_out                          false
% 27.47/3.99  
% 27.47/3.99  ------ Global Options
% 27.47/3.99  
% 27.47/3.99  --schedule                              default
% 27.47/3.99  --add_important_lit                     false
% 27.47/3.99  --prop_solver_per_cl                    1000
% 27.47/3.99  --min_unsat_core                        false
% 27.47/3.99  --soft_assumptions                      false
% 27.47/3.99  --soft_lemma_size                       3
% 27.47/3.99  --prop_impl_unit_size                   0
% 27.47/3.99  --prop_impl_unit                        []
% 27.47/3.99  --share_sel_clauses                     true
% 27.47/3.99  --reset_solvers                         false
% 27.47/3.99  --bc_imp_inh                            [conj_cone]
% 27.47/3.99  --conj_cone_tolerance                   3.
% 27.47/3.99  --extra_neg_conj                        none
% 27.47/3.99  --large_theory_mode                     true
% 27.47/3.99  --prolific_symb_bound                   200
% 27.47/3.99  --lt_threshold                          2000
% 27.47/3.99  --clause_weak_htbl                      true
% 27.47/3.99  --gc_record_bc_elim                     false
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing Options
% 27.47/3.99  
% 27.47/3.99  --preprocessing_flag                    true
% 27.47/3.99  --time_out_prep_mult                    0.1
% 27.47/3.99  --splitting_mode                        input
% 27.47/3.99  --splitting_grd                         true
% 27.47/3.99  --splitting_cvd                         false
% 27.47/3.99  --splitting_cvd_svl                     false
% 27.47/3.99  --splitting_nvd                         32
% 27.47/3.99  --sub_typing                            true
% 27.47/3.99  --prep_gs_sim                           true
% 27.47/3.99  --prep_unflatten                        true
% 27.47/3.99  --prep_res_sim                          true
% 27.47/3.99  --prep_upred                            true
% 27.47/3.99  --prep_sem_filter                       exhaustive
% 27.47/3.99  --prep_sem_filter_out                   false
% 27.47/3.99  --pred_elim                             true
% 27.47/3.99  --res_sim_input                         true
% 27.47/3.99  --eq_ax_congr_red                       true
% 27.47/3.99  --pure_diseq_elim                       true
% 27.47/3.99  --brand_transform                       false
% 27.47/3.99  --non_eq_to_eq                          false
% 27.47/3.99  --prep_def_merge                        true
% 27.47/3.99  --prep_def_merge_prop_impl              false
% 27.47/3.99  --prep_def_merge_mbd                    true
% 27.47/3.99  --prep_def_merge_tr_red                 false
% 27.47/3.99  --prep_def_merge_tr_cl                  false
% 27.47/3.99  --smt_preprocessing                     true
% 27.47/3.99  --smt_ac_axioms                         fast
% 27.47/3.99  --preprocessed_out                      false
% 27.47/3.99  --preprocessed_stats                    false
% 27.47/3.99  
% 27.47/3.99  ------ Abstraction refinement Options
% 27.47/3.99  
% 27.47/3.99  --abstr_ref                             []
% 27.47/3.99  --abstr_ref_prep                        false
% 27.47/3.99  --abstr_ref_until_sat                   false
% 27.47/3.99  --abstr_ref_sig_restrict                funpre
% 27.47/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.47/3.99  --abstr_ref_under                       []
% 27.47/3.99  
% 27.47/3.99  ------ SAT Options
% 27.47/3.99  
% 27.47/3.99  --sat_mode                              false
% 27.47/3.99  --sat_fm_restart_options                ""
% 27.47/3.99  --sat_gr_def                            false
% 27.47/3.99  --sat_epr_types                         true
% 27.47/3.99  --sat_non_cyclic_types                  false
% 27.47/3.99  --sat_finite_models                     false
% 27.47/3.99  --sat_fm_lemmas                         false
% 27.47/3.99  --sat_fm_prep                           false
% 27.47/3.99  --sat_fm_uc_incr                        true
% 27.47/3.99  --sat_out_model                         small
% 27.47/3.99  --sat_out_clauses                       false
% 27.47/3.99  
% 27.47/3.99  ------ QBF Options
% 27.47/3.99  
% 27.47/3.99  --qbf_mode                              false
% 27.47/3.99  --qbf_elim_univ                         false
% 27.47/3.99  --qbf_dom_inst                          none
% 27.47/3.99  --qbf_dom_pre_inst                      false
% 27.47/3.99  --qbf_sk_in                             false
% 27.47/3.99  --qbf_pred_elim                         true
% 27.47/3.99  --qbf_split                             512
% 27.47/3.99  
% 27.47/3.99  ------ BMC1 Options
% 27.47/3.99  
% 27.47/3.99  --bmc1_incremental                      false
% 27.47/3.99  --bmc1_axioms                           reachable_all
% 27.47/3.99  --bmc1_min_bound                        0
% 27.47/3.99  --bmc1_max_bound                        -1
% 27.47/3.99  --bmc1_max_bound_default                -1
% 27.47/3.99  --bmc1_symbol_reachability              true
% 27.47/3.99  --bmc1_property_lemmas                  false
% 27.47/3.99  --bmc1_k_induction                      false
% 27.47/3.99  --bmc1_non_equiv_states                 false
% 27.47/3.99  --bmc1_deadlock                         false
% 27.47/3.99  --bmc1_ucm                              false
% 27.47/3.99  --bmc1_add_unsat_core                   none
% 27.47/3.99  --bmc1_unsat_core_children              false
% 27.47/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.47/3.99  --bmc1_out_stat                         full
% 27.47/3.99  --bmc1_ground_init                      false
% 27.47/3.99  --bmc1_pre_inst_next_state              false
% 27.47/3.99  --bmc1_pre_inst_state                   false
% 27.47/3.99  --bmc1_pre_inst_reach_state             false
% 27.47/3.99  --bmc1_out_unsat_core                   false
% 27.47/3.99  --bmc1_aig_witness_out                  false
% 27.47/3.99  --bmc1_verbose                          false
% 27.47/3.99  --bmc1_dump_clauses_tptp                false
% 27.47/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.47/3.99  --bmc1_dump_file                        -
% 27.47/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.47/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.47/3.99  --bmc1_ucm_extend_mode                  1
% 27.47/3.99  --bmc1_ucm_init_mode                    2
% 27.47/3.99  --bmc1_ucm_cone_mode                    none
% 27.47/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.47/3.99  --bmc1_ucm_relax_model                  4
% 27.47/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.47/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.47/3.99  --bmc1_ucm_layered_model                none
% 27.47/3.99  --bmc1_ucm_max_lemma_size               10
% 27.47/3.99  
% 27.47/3.99  ------ AIG Options
% 27.47/3.99  
% 27.47/3.99  --aig_mode                              false
% 27.47/3.99  
% 27.47/3.99  ------ Instantiation Options
% 27.47/3.99  
% 27.47/3.99  --instantiation_flag                    true
% 27.47/3.99  --inst_sos_flag                         true
% 27.47/3.99  --inst_sos_phase                        true
% 27.47/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.47/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.47/3.99  --inst_lit_sel_side                     num_symb
% 27.47/3.99  --inst_solver_per_active                1400
% 27.47/3.99  --inst_solver_calls_frac                1.
% 27.47/3.99  --inst_passive_queue_type               priority_queues
% 27.47/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.47/3.99  --inst_passive_queues_freq              [25;2]
% 27.47/3.99  --inst_dismatching                      true
% 27.47/3.99  --inst_eager_unprocessed_to_passive     true
% 27.47/3.99  --inst_prop_sim_given                   true
% 27.47/3.99  --inst_prop_sim_new                     false
% 27.47/3.99  --inst_subs_new                         false
% 27.47/3.99  --inst_eq_res_simp                      false
% 27.47/3.99  --inst_subs_given                       false
% 27.47/3.99  --inst_orphan_elimination               true
% 27.47/3.99  --inst_learning_loop_flag               true
% 27.47/3.99  --inst_learning_start                   3000
% 27.47/3.99  --inst_learning_factor                  2
% 27.47/3.99  --inst_start_prop_sim_after_learn       3
% 27.47/3.99  --inst_sel_renew                        solver
% 27.47/3.99  --inst_lit_activity_flag                true
% 27.47/3.99  --inst_restr_to_given                   false
% 27.47/3.99  --inst_activity_threshold               500
% 27.47/3.99  --inst_out_proof                        true
% 27.47/3.99  
% 27.47/3.99  ------ Resolution Options
% 27.47/3.99  
% 27.47/3.99  --resolution_flag                       true
% 27.47/3.99  --res_lit_sel                           adaptive
% 27.47/3.99  --res_lit_sel_side                      none
% 27.47/3.99  --res_ordering                          kbo
% 27.47/3.99  --res_to_prop_solver                    active
% 27.47/3.99  --res_prop_simpl_new                    false
% 27.47/3.99  --res_prop_simpl_given                  true
% 27.47/3.99  --res_passive_queue_type                priority_queues
% 27.47/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.47/3.99  --res_passive_queues_freq               [15;5]
% 27.47/3.99  --res_forward_subs                      full
% 27.47/3.99  --res_backward_subs                     full
% 27.47/3.99  --res_forward_subs_resolution           true
% 27.47/3.99  --res_backward_subs_resolution          true
% 27.47/3.99  --res_orphan_elimination                true
% 27.47/3.99  --res_time_limit                        2.
% 27.47/3.99  --res_out_proof                         true
% 27.47/3.99  
% 27.47/3.99  ------ Superposition Options
% 27.47/3.99  
% 27.47/3.99  --superposition_flag                    true
% 27.47/3.99  --sup_passive_queue_type                priority_queues
% 27.47/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.47/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.47/3.99  --demod_completeness_check              fast
% 27.47/3.99  --demod_use_ground                      true
% 27.47/3.99  --sup_to_prop_solver                    passive
% 27.47/3.99  --sup_prop_simpl_new                    true
% 27.47/3.99  --sup_prop_simpl_given                  true
% 27.47/3.99  --sup_fun_splitting                     true
% 27.47/3.99  --sup_smt_interval                      50000
% 27.47/3.99  
% 27.47/3.99  ------ Superposition Simplification Setup
% 27.47/3.99  
% 27.47/3.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.47/3.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.47/3.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.47/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.47/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.47/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.47/3.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.47/3.99  --sup_immed_triv                        [TrivRules]
% 27.47/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_immed_bw_main                     []
% 27.47/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.47/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.47/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_input_bw                          []
% 27.47/3.99  
% 27.47/3.99  ------ Combination Options
% 27.47/3.99  
% 27.47/3.99  --comb_res_mult                         3
% 27.47/3.99  --comb_sup_mult                         2
% 27.47/3.99  --comb_inst_mult                        10
% 27.47/3.99  
% 27.47/3.99  ------ Debug Options
% 27.47/3.99  
% 27.47/3.99  --dbg_backtrace                         false
% 27.47/3.99  --dbg_dump_prop_clauses                 false
% 27.47/3.99  --dbg_dump_prop_clauses_file            -
% 27.47/3.99  --dbg_out_stat                          false
% 27.47/3.99  ------ Parsing...
% 27.47/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.47/3.99  ------ Proving...
% 27.47/3.99  ------ Problem Properties 
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  clauses                                 18
% 27.47/3.99  conjectures                             2
% 27.47/3.99  EPR                                     5
% 27.47/3.99  Horn                                    18
% 27.47/3.99  unary                                   11
% 27.47/3.99  binary                                  2
% 27.47/3.99  lits                                    32
% 27.47/3.99  lits eq                                 13
% 27.47/3.99  fd_pure                                 0
% 27.47/3.99  fd_pseudo                               0
% 27.47/3.99  fd_cond                                 0
% 27.47/3.99  fd_pseudo_cond                          1
% 27.47/3.99  AC symbols                              0
% 27.47/3.99  
% 27.47/3.99  ------ Schedule dynamic 5 is on 
% 27.47/3.99  
% 27.47/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  ------ 
% 27.47/3.99  Current options:
% 27.47/3.99  ------ 
% 27.47/3.99  
% 27.47/3.99  ------ Input Options
% 27.47/3.99  
% 27.47/3.99  --out_options                           all
% 27.47/3.99  --tptp_safe_out                         true
% 27.47/3.99  --problem_path                          ""
% 27.47/3.99  --include_path                          ""
% 27.47/3.99  --clausifier                            res/vclausify_rel
% 27.47/3.99  --clausifier_options                    ""
% 27.47/3.99  --stdin                                 false
% 27.47/3.99  --stats_out                             all
% 27.47/3.99  
% 27.47/3.99  ------ General Options
% 27.47/3.99  
% 27.47/3.99  --fof                                   false
% 27.47/3.99  --time_out_real                         305.
% 27.47/3.99  --time_out_virtual                      -1.
% 27.47/3.99  --symbol_type_check                     false
% 27.47/3.99  --clausify_out                          false
% 27.47/3.99  --sig_cnt_out                           false
% 27.47/3.99  --trig_cnt_out                          false
% 27.47/3.99  --trig_cnt_out_tolerance                1.
% 27.47/3.99  --trig_cnt_out_sk_spl                   false
% 27.47/3.99  --abstr_cl_out                          false
% 27.47/3.99  
% 27.47/3.99  ------ Global Options
% 27.47/3.99  
% 27.47/3.99  --schedule                              default
% 27.47/3.99  --add_important_lit                     false
% 27.47/3.99  --prop_solver_per_cl                    1000
% 27.47/3.99  --min_unsat_core                        false
% 27.47/3.99  --soft_assumptions                      false
% 27.47/3.99  --soft_lemma_size                       3
% 27.47/3.99  --prop_impl_unit_size                   0
% 27.47/3.99  --prop_impl_unit                        []
% 27.47/3.99  --share_sel_clauses                     true
% 27.47/3.99  --reset_solvers                         false
% 27.47/3.99  --bc_imp_inh                            [conj_cone]
% 27.47/3.99  --conj_cone_tolerance                   3.
% 27.47/3.99  --extra_neg_conj                        none
% 27.47/3.99  --large_theory_mode                     true
% 27.47/3.99  --prolific_symb_bound                   200
% 27.47/3.99  --lt_threshold                          2000
% 27.47/3.99  --clause_weak_htbl                      true
% 27.47/3.99  --gc_record_bc_elim                     false
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing Options
% 27.47/3.99  
% 27.47/3.99  --preprocessing_flag                    true
% 27.47/3.99  --time_out_prep_mult                    0.1
% 27.47/3.99  --splitting_mode                        input
% 27.47/3.99  --splitting_grd                         true
% 27.47/3.99  --splitting_cvd                         false
% 27.47/3.99  --splitting_cvd_svl                     false
% 27.47/3.99  --splitting_nvd                         32
% 27.47/3.99  --sub_typing                            true
% 27.47/3.99  --prep_gs_sim                           true
% 27.47/3.99  --prep_unflatten                        true
% 27.47/3.99  --prep_res_sim                          true
% 27.47/3.99  --prep_upred                            true
% 27.47/3.99  --prep_sem_filter                       exhaustive
% 27.47/3.99  --prep_sem_filter_out                   false
% 27.47/3.99  --pred_elim                             true
% 27.47/3.99  --res_sim_input                         true
% 27.47/3.99  --eq_ax_congr_red                       true
% 27.47/3.99  --pure_diseq_elim                       true
% 27.47/3.99  --brand_transform                       false
% 27.47/3.99  --non_eq_to_eq                          false
% 27.47/3.99  --prep_def_merge                        true
% 27.47/3.99  --prep_def_merge_prop_impl              false
% 27.47/3.99  --prep_def_merge_mbd                    true
% 27.47/3.99  --prep_def_merge_tr_red                 false
% 27.47/3.99  --prep_def_merge_tr_cl                  false
% 27.47/3.99  --smt_preprocessing                     true
% 27.47/3.99  --smt_ac_axioms                         fast
% 27.47/3.99  --preprocessed_out                      false
% 27.47/3.99  --preprocessed_stats                    false
% 27.47/3.99  
% 27.47/3.99  ------ Abstraction refinement Options
% 27.47/3.99  
% 27.47/3.99  --abstr_ref                             []
% 27.47/3.99  --abstr_ref_prep                        false
% 27.47/3.99  --abstr_ref_until_sat                   false
% 27.47/3.99  --abstr_ref_sig_restrict                funpre
% 27.47/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.47/3.99  --abstr_ref_under                       []
% 27.47/3.99  
% 27.47/3.99  ------ SAT Options
% 27.47/3.99  
% 27.47/3.99  --sat_mode                              false
% 27.47/3.99  --sat_fm_restart_options                ""
% 27.47/3.99  --sat_gr_def                            false
% 27.47/3.99  --sat_epr_types                         true
% 27.47/3.99  --sat_non_cyclic_types                  false
% 27.47/3.99  --sat_finite_models                     false
% 27.47/3.99  --sat_fm_lemmas                         false
% 27.47/3.99  --sat_fm_prep                           false
% 27.47/3.99  --sat_fm_uc_incr                        true
% 27.47/3.99  --sat_out_model                         small
% 27.47/3.99  --sat_out_clauses                       false
% 27.47/3.99  
% 27.47/3.99  ------ QBF Options
% 27.47/3.99  
% 27.47/3.99  --qbf_mode                              false
% 27.47/3.99  --qbf_elim_univ                         false
% 27.47/3.99  --qbf_dom_inst                          none
% 27.47/3.99  --qbf_dom_pre_inst                      false
% 27.47/3.99  --qbf_sk_in                             false
% 27.47/3.99  --qbf_pred_elim                         true
% 27.47/3.99  --qbf_split                             512
% 27.47/3.99  
% 27.47/3.99  ------ BMC1 Options
% 27.47/3.99  
% 27.47/3.99  --bmc1_incremental                      false
% 27.47/3.99  --bmc1_axioms                           reachable_all
% 27.47/3.99  --bmc1_min_bound                        0
% 27.47/3.99  --bmc1_max_bound                        -1
% 27.47/3.99  --bmc1_max_bound_default                -1
% 27.47/3.99  --bmc1_symbol_reachability              true
% 27.47/3.99  --bmc1_property_lemmas                  false
% 27.47/3.99  --bmc1_k_induction                      false
% 27.47/3.99  --bmc1_non_equiv_states                 false
% 27.47/3.99  --bmc1_deadlock                         false
% 27.47/3.99  --bmc1_ucm                              false
% 27.47/3.99  --bmc1_add_unsat_core                   none
% 27.47/3.99  --bmc1_unsat_core_children              false
% 27.47/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.47/3.99  --bmc1_out_stat                         full
% 27.47/3.99  --bmc1_ground_init                      false
% 27.47/3.99  --bmc1_pre_inst_next_state              false
% 27.47/3.99  --bmc1_pre_inst_state                   false
% 27.47/3.99  --bmc1_pre_inst_reach_state             false
% 27.47/3.99  --bmc1_out_unsat_core                   false
% 27.47/3.99  --bmc1_aig_witness_out                  false
% 27.47/3.99  --bmc1_verbose                          false
% 27.47/3.99  --bmc1_dump_clauses_tptp                false
% 27.47/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.47/3.99  --bmc1_dump_file                        -
% 27.47/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.47/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.47/3.99  --bmc1_ucm_extend_mode                  1
% 27.47/3.99  --bmc1_ucm_init_mode                    2
% 27.47/3.99  --bmc1_ucm_cone_mode                    none
% 27.47/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.47/3.99  --bmc1_ucm_relax_model                  4
% 27.47/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.47/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.47/3.99  --bmc1_ucm_layered_model                none
% 27.47/3.99  --bmc1_ucm_max_lemma_size               10
% 27.47/3.99  
% 27.47/3.99  ------ AIG Options
% 27.47/3.99  
% 27.47/3.99  --aig_mode                              false
% 27.47/3.99  
% 27.47/3.99  ------ Instantiation Options
% 27.47/3.99  
% 27.47/3.99  --instantiation_flag                    true
% 27.47/3.99  --inst_sos_flag                         true
% 27.47/3.99  --inst_sos_phase                        true
% 27.47/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.47/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.47/3.99  --inst_lit_sel_side                     none
% 27.47/3.99  --inst_solver_per_active                1400
% 27.47/3.99  --inst_solver_calls_frac                1.
% 27.47/3.99  --inst_passive_queue_type               priority_queues
% 27.47/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.47/3.99  --inst_passive_queues_freq              [25;2]
% 27.47/3.99  --inst_dismatching                      true
% 27.47/3.99  --inst_eager_unprocessed_to_passive     true
% 27.47/3.99  --inst_prop_sim_given                   true
% 27.47/3.99  --inst_prop_sim_new                     false
% 27.47/3.99  --inst_subs_new                         false
% 27.47/3.99  --inst_eq_res_simp                      false
% 27.47/3.99  --inst_subs_given                       false
% 27.47/3.99  --inst_orphan_elimination               true
% 27.47/3.99  --inst_learning_loop_flag               true
% 27.47/3.99  --inst_learning_start                   3000
% 27.47/3.99  --inst_learning_factor                  2
% 27.47/3.99  --inst_start_prop_sim_after_learn       3
% 27.47/3.99  --inst_sel_renew                        solver
% 27.47/3.99  --inst_lit_activity_flag                true
% 27.47/3.99  --inst_restr_to_given                   false
% 27.47/3.99  --inst_activity_threshold               500
% 27.47/3.99  --inst_out_proof                        true
% 27.47/3.99  
% 27.47/3.99  ------ Resolution Options
% 27.47/3.99  
% 27.47/3.99  --resolution_flag                       false
% 27.47/3.99  --res_lit_sel                           adaptive
% 27.47/3.99  --res_lit_sel_side                      none
% 27.47/3.99  --res_ordering                          kbo
% 27.47/3.99  --res_to_prop_solver                    active
% 27.47/3.99  --res_prop_simpl_new                    false
% 27.47/3.99  --res_prop_simpl_given                  true
% 27.47/3.99  --res_passive_queue_type                priority_queues
% 27.47/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.47/3.99  --res_passive_queues_freq               [15;5]
% 27.47/3.99  --res_forward_subs                      full
% 27.47/3.99  --res_backward_subs                     full
% 27.47/3.99  --res_forward_subs_resolution           true
% 27.47/3.99  --res_backward_subs_resolution          true
% 27.47/3.99  --res_orphan_elimination                true
% 27.47/3.99  --res_time_limit                        2.
% 27.47/3.99  --res_out_proof                         true
% 27.47/3.99  
% 27.47/3.99  ------ Superposition Options
% 27.47/3.99  
% 27.47/3.99  --superposition_flag                    true
% 27.47/3.99  --sup_passive_queue_type                priority_queues
% 27.47/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.47/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.47/3.99  --demod_completeness_check              fast
% 27.47/3.99  --demod_use_ground                      true
% 27.47/3.99  --sup_to_prop_solver                    passive
% 27.47/3.99  --sup_prop_simpl_new                    true
% 27.47/3.99  --sup_prop_simpl_given                  true
% 27.47/3.99  --sup_fun_splitting                     true
% 27.47/3.99  --sup_smt_interval                      50000
% 27.47/3.99  
% 27.47/3.99  ------ Superposition Simplification Setup
% 27.47/3.99  
% 27.47/3.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.47/3.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.47/3.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.47/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.47/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.47/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.47/3.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.47/3.99  --sup_immed_triv                        [TrivRules]
% 27.47/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_immed_bw_main                     []
% 27.47/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.47/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.47/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_input_bw                          []
% 27.47/3.99  
% 27.47/3.99  ------ Combination Options
% 27.47/3.99  
% 27.47/3.99  --comb_res_mult                         3
% 27.47/3.99  --comb_sup_mult                         2
% 27.47/3.99  --comb_inst_mult                        10
% 27.47/3.99  
% 27.47/3.99  ------ Debug Options
% 27.47/3.99  
% 27.47/3.99  --dbg_backtrace                         false
% 27.47/3.99  --dbg_dump_prop_clauses                 false
% 27.47/3.99  --dbg_dump_prop_clauses_file            -
% 27.47/3.99  --dbg_out_stat                          false
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  ------ Proving...
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  % SZS status Theorem for theBenchmark.p
% 27.47/3.99  
% 27.47/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.47/3.99  
% 27.47/3.99  fof(f1,axiom,(
% 27.47/3.99    v1_xboole_0(k1_xboole_0)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f39,plain,(
% 27.47/3.99    v1_xboole_0(k1_xboole_0)),
% 27.47/3.99    inference(cnf_transformation,[],[f1])).
% 27.47/3.99  
% 27.47/3.99  fof(f16,axiom,(
% 27.47/3.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f26,plain,(
% 27.47/3.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 27.47/3.99    inference(ennf_transformation,[],[f16])).
% 27.47/3.99  
% 27.47/3.99  fof(f57,plain,(
% 27.47/3.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f26])).
% 27.47/3.99  
% 27.47/3.99  fof(f23,conjecture,(
% 27.47/3.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f24,negated_conjecture,(
% 27.47/3.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 27.47/3.99    inference(negated_conjecture,[],[f23])).
% 27.47/3.99  
% 27.47/3.99  fof(f34,plain,(
% 27.47/3.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 27.47/3.99    inference(ennf_transformation,[],[f24])).
% 27.47/3.99  
% 27.47/3.99  fof(f37,plain,(
% 27.47/3.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 27.47/3.99    introduced(choice_axiom,[])).
% 27.47/3.99  
% 27.47/3.99  fof(f38,plain,(
% 27.47/3.99    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 27.47/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f37])).
% 27.47/3.99  
% 27.47/3.99  fof(f65,plain,(
% 27.47/3.99    v1_relat_1(sK0)),
% 27.47/3.99    inference(cnf_transformation,[],[f38])).
% 27.47/3.99  
% 27.47/3.99  fof(f17,axiom,(
% 27.47/3.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f27,plain,(
% 27.47/3.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 27.47/3.99    inference(ennf_transformation,[],[f17])).
% 27.47/3.99  
% 27.47/3.99  fof(f28,plain,(
% 27.47/3.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(flattening,[],[f27])).
% 27.47/3.99  
% 27.47/3.99  fof(f58,plain,(
% 27.47/3.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f28])).
% 27.47/3.99  
% 27.47/3.99  fof(f18,axiom,(
% 27.47/3.99    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f29,plain,(
% 27.47/3.99    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 27.47/3.99    inference(ennf_transformation,[],[f18])).
% 27.47/3.99  
% 27.47/3.99  fof(f59,plain,(
% 27.47/3.99    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f29])).
% 27.47/3.99  
% 27.47/3.99  fof(f15,axiom,(
% 27.47/3.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f56,plain,(
% 27.47/3.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 27.47/3.99    inference(cnf_transformation,[],[f15])).
% 27.47/3.99  
% 27.47/3.99  fof(f8,axiom,(
% 27.47/3.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f48,plain,(
% 27.47/3.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f8])).
% 27.47/3.99  
% 27.47/3.99  fof(f9,axiom,(
% 27.47/3.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f49,plain,(
% 27.47/3.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f9])).
% 27.47/3.99  
% 27.47/3.99  fof(f10,axiom,(
% 27.47/3.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f50,plain,(
% 27.47/3.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f10])).
% 27.47/3.99  
% 27.47/3.99  fof(f11,axiom,(
% 27.47/3.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f51,plain,(
% 27.47/3.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f11])).
% 27.47/3.99  
% 27.47/3.99  fof(f12,axiom,(
% 27.47/3.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f52,plain,(
% 27.47/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f12])).
% 27.47/3.99  
% 27.47/3.99  fof(f13,axiom,(
% 27.47/3.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f53,plain,(
% 27.47/3.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f13])).
% 27.47/3.99  
% 27.47/3.99  fof(f67,plain,(
% 27.47/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 27.47/3.99    inference(definition_unfolding,[],[f52,f53])).
% 27.47/3.99  
% 27.47/3.99  fof(f68,plain,(
% 27.47/3.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 27.47/3.99    inference(definition_unfolding,[],[f51,f67])).
% 27.47/3.99  
% 27.47/3.99  fof(f69,plain,(
% 27.47/3.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.47/3.99    inference(definition_unfolding,[],[f50,f68])).
% 27.47/3.99  
% 27.47/3.99  fof(f70,plain,(
% 27.47/3.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 27.47/3.99    inference(definition_unfolding,[],[f49,f69])).
% 27.47/3.99  
% 27.47/3.99  fof(f71,plain,(
% 27.47/3.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 27.47/3.99    inference(definition_unfolding,[],[f48,f70])).
% 27.47/3.99  
% 27.47/3.99  fof(f72,plain,(
% 27.47/3.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 27.47/3.99    inference(definition_unfolding,[],[f56,f71])).
% 27.47/3.99  
% 27.47/3.99  fof(f78,plain,(
% 27.47/3.99    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(definition_unfolding,[],[f59,f72])).
% 27.47/3.99  
% 27.47/3.99  fof(f21,axiom,(
% 27.47/3.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f33,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(ennf_transformation,[],[f21])).
% 27.47/3.99  
% 27.47/3.99  fof(f62,plain,(
% 27.47/3.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f33])).
% 27.47/3.99  
% 27.47/3.99  fof(f22,axiom,(
% 27.47/3.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f64,plain,(
% 27.47/3.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 27.47/3.99    inference(cnf_transformation,[],[f22])).
% 27.47/3.99  
% 27.47/3.99  fof(f19,axiom,(
% 27.47/3.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f30,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(ennf_transformation,[],[f19])).
% 27.47/3.99  
% 27.47/3.99  fof(f60,plain,(
% 27.47/3.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f6,axiom,(
% 27.47/3.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f46,plain,(
% 27.47/3.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f6])).
% 27.47/3.99  
% 27.47/3.99  fof(f3,axiom,(
% 27.47/3.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f35,plain,(
% 27.47/3.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.47/3.99    inference(nnf_transformation,[],[f3])).
% 27.47/3.99  
% 27.47/3.99  fof(f36,plain,(
% 27.47/3.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.47/3.99    inference(flattening,[],[f35])).
% 27.47/3.99  
% 27.47/3.99  fof(f43,plain,(
% 27.47/3.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f36])).
% 27.47/3.99  
% 27.47/3.99  fof(f20,axiom,(
% 27.47/3.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f31,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(ennf_transformation,[],[f20])).
% 27.47/3.99  
% 27.47/3.99  fof(f32,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(flattening,[],[f31])).
% 27.47/3.99  
% 27.47/3.99  fof(f61,plain,(
% 27.47/3.99    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f32])).
% 27.47/3.99  
% 27.47/3.99  fof(f63,plain,(
% 27.47/3.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 27.47/3.99    inference(cnf_transformation,[],[f22])).
% 27.47/3.99  
% 27.47/3.99  fof(f5,axiom,(
% 27.47/3.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f45,plain,(
% 27.47/3.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f5])).
% 27.47/3.99  
% 27.47/3.99  fof(f75,plain,(
% 27.47/3.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 27.47/3.99    inference(definition_unfolding,[],[f45,f72])).
% 27.47/3.99  
% 27.47/3.99  fof(f14,axiom,(
% 27.47/3.99    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f54,plain,(
% 27.47/3.99    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f14])).
% 27.47/3.99  
% 27.47/3.99  fof(f4,axiom,(
% 27.47/3.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f44,plain,(
% 27.47/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.47/3.99    inference(cnf_transformation,[],[f4])).
% 27.47/3.99  
% 27.47/3.99  fof(f73,plain,(
% 27.47/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 27.47/3.99    inference(definition_unfolding,[],[f44,f72])).
% 27.47/3.99  
% 27.47/3.99  fof(f77,plain,(
% 27.47/3.99    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2)) )),
% 27.47/3.99    inference(definition_unfolding,[],[f54,f73,f73])).
% 27.47/3.99  
% 27.47/3.99  fof(f55,plain,(
% 27.47/3.99    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))) )),
% 27.47/3.99    inference(cnf_transformation,[],[f14])).
% 27.47/3.99  
% 27.47/3.99  fof(f76,plain,(
% 27.47/3.99    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 27.47/3.99    inference(definition_unfolding,[],[f55,f73,f73])).
% 27.47/3.99  
% 27.47/3.99  fof(f2,axiom,(
% 27.47/3.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f25,plain,(
% 27.47/3.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 27.47/3.99    inference(rectify,[],[f2])).
% 27.47/3.99  
% 27.47/3.99  fof(f40,plain,(
% 27.47/3.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 27.47/3.99    inference(cnf_transformation,[],[f25])).
% 27.47/3.99  
% 27.47/3.99  fof(f74,plain,(
% 27.47/3.99    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 27.47/3.99    inference(definition_unfolding,[],[f40,f72])).
% 27.47/3.99  
% 27.47/3.99  fof(f7,axiom,(
% 27.47/3.99    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f47,plain,(
% 27.47/3.99    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f7])).
% 27.47/3.99  
% 27.47/3.99  fof(f66,plain,(
% 27.47/3.99    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 27.47/3.99    inference(cnf_transformation,[],[f38])).
% 27.47/3.99  
% 27.47/3.99  cnf(c_0,plain,
% 27.47/3.99      ( v1_xboole_0(k1_xboole_0) ),
% 27.47/3.99      inference(cnf_transformation,[],[f39]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_10,plain,
% 27.47/3.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 27.47/3.99      inference(cnf_transformation,[],[f57]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_147,plain,
% 27.47/3.99      ( v1_relat_1(X0) | k1_xboole_0 != X0 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_148,plain,
% 27.47/3.99      ( v1_relat_1(k1_xboole_0) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_147]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_409,plain,
% 27.47/3.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_19,negated_conjecture,
% 27.47/3.99      ( v1_relat_1(sK0) ),
% 27.47/3.99      inference(cnf_transformation,[],[f65]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_410,plain,
% 27.47/3.99      ( v1_relat_1(sK0) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_11,plain,
% 27.47/3.99      ( ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 27.47/3.99      inference(cnf_transformation,[],[f58]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_415,plain,
% 27.47/3.99      ( v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(X1) != iProver_top
% 27.47/3.99      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_12,plain,
% 27.47/3.99      ( ~ v1_relat_1(X0)
% 27.47/3.99      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 27.47/3.99      inference(cnf_transformation,[],[f78]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_414,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2490,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 27.47/3.99      | v1_relat_1(X1) != iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_415,c_414]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_52715,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0))))) = k5_relat_1(sK0,X0)
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_410,c_2490]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_53883,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_409,c_52715]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_15,plain,
% 27.47/3.99      ( ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_relat_1(X2)
% 27.47/3.99      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 27.47/3.99      inference(cnf_transformation,[],[f62]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_411,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 27.47/3.99      | v1_relat_1(X1) != iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(X2) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_756,plain,
% 27.47/3.99      ( k5_relat_1(sK0,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK0,X0),X1)
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(X1) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_410,c_411]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_942,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X0) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,X0))
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_409,c_756]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1194,plain,
% 27.47/3.99      ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_410,c_942]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1908,plain,
% 27.47/3.99      ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) = iProver_top
% 27.47/3.99      | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 27.47/3.99      | v1_relat_1(sK0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_1194,c_415]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_20,plain,
% 27.47/3.99      ( v1_relat_1(sK0) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_36,plain,
% 27.47/3.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_38,plain,
% 27.47/3.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 27.47/3.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_36]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_51,plain,
% 27.47/3.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_790,plain,
% 27.47/3.99      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 27.47/3.99      | ~ v1_relat_1(sK0)
% 27.47/3.99      | ~ v1_relat_1(k1_xboole_0) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_11]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_791,plain,
% 27.47/3.99      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 27.47/3.99      | v1_relat_1(sK0) != iProver_top
% 27.47/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2015,plain,
% 27.47/3.99      ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_1908,c_20,c_38,c_51,c_791]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_16,plain,
% 27.47/3.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 27.47/3.99      inference(cnf_transformation,[],[f64]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_13,plain,
% 27.47/3.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_relat_1(X0) ),
% 27.47/3.99      inference(cnf_transformation,[],[f60]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_413,plain,
% 27.47/3.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(X1) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2301,plain,
% 27.47/3.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_16,c_413]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2476,plain,
% 27.47/3.99      ( v1_relat_1(X0) != iProver_top
% 27.47/3.99      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_2301,c_38,c_51]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2477,plain,
% 27.47/3.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_2476]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_6,plain,
% 27.47/3.99      ( r1_tarski(k1_xboole_0,X0) ),
% 27.47/3.99      inference(cnf_transformation,[],[f46]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_416,plain,
% 27.47/3.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2,plain,
% 27.47/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.47/3.99      inference(cnf_transformation,[],[f43]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_418,plain,
% 27.47/3.99      ( X0 = X1
% 27.47/3.99      | r1_tarski(X0,X1) != iProver_top
% 27.47/3.99      | r1_tarski(X1,X0) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1787,plain,
% 27.47/3.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_416,c_418]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2483,plain,
% 27.47/3.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_2477,c_1787]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_50242,plain,
% 27.47/3.99      ( k2_relat_1(k5_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)) = k1_xboole_0 ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_2015,c_2483]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1912,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(X0,X1),k5_relat_1(X2,X3)) = k5_relat_1(k5_relat_1(k5_relat_1(X0,X1),X2),X3)
% 27.47/3.99      | v1_relat_1(X1) != iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(X2) != iProver_top
% 27.47/3.99      | v1_relat_1(X3) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_415,c_411]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_17393,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(k5_relat_1(sK0,X0),X1),X2) = k5_relat_1(k5_relat_1(sK0,X0),k5_relat_1(X1,X2))
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(X1) != iProver_top
% 27.47/3.99      | v1_relat_1(X2) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_410,c_1912]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_18349,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X0),X1) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(X0,X1))
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(X1) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_409,c_17393]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_25428,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0),X0) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,X0))
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_410,c_18349]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_25446,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,X0)) = k5_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),X0)
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_25428,c_1194]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_25495,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_409,c_25446]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1909,plain,
% 27.47/3.99      ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(X0,X1))) = k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(X0,X1))
% 27.47/3.99      | v1_relat_1(X1) != iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_415,c_942]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_12666,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,X0)) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(sK0,X0)))
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_410,c_1909]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_13136,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_409,c_12666]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_757,plain,
% 27.47/3.99      ( k5_relat_1(k1_xboole_0,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k1_xboole_0,X0),X1)
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(X1) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_409,c_411]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2896,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(k1_xboole_0,sK0),X0) = k5_relat_1(k1_xboole_0,k5_relat_1(sK0,X0))
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_410,c_757]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_3195,plain,
% 27.47/3.99      ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_409,c_2896]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_3358,plain,
% 27.47/3.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 27.47/3.99      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 27.47/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_3195,c_415]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_10853,plain,
% 27.47/3.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 27.47/3.99      | v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_3358,c_38,c_51]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_10854,plain,
% 27.47/3.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 27.47/3.99      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_10853]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_10869,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)))))) = k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))
% 27.47/3.99      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_10854,c_414]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_14,plain,
% 27.47/3.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 27.47/3.99      inference(cnf_transformation,[],[f61]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_412,plain,
% 27.47/3.99      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 27.47/3.99      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(X1) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1461,plain,
% 27.47/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 27.47/3.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_16,c_412]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_17,plain,
% 27.47/3.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 27.47/3.99      inference(cnf_transformation,[],[f63]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1463,plain,
% 27.47/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 27.47/3.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top
% 27.47/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_1461,c_17]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2914,plain,
% 27.47/3.99      ( v1_relat_1(X0) != iProver_top
% 27.47/3.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 27.47/3.99      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_1463,c_38,c_51]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2915,plain,
% 27.47/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 27.47/3.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_2914]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2918,plain,
% 27.47/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_416,c_2915]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_7015,plain,
% 27.47/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(X0,X1))) = k1_xboole_0
% 27.47/3.99      | v1_relat_1(X1) != iProver_top
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_415,c_2918]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_8433,plain,
% 27.47/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,X0))) = k1_xboole_0
% 27.47/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_410,c_7015]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_8656,plain,
% 27.47/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_409,c_8433]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_10876,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)))))) = k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))
% 27.47/3.99      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_10869,c_8656]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_5,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.47/3.99      inference(cnf_transformation,[],[f75]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_9,plain,
% 27.47/3.99      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
% 27.47/3.99      inference(cnf_transformation,[],[f77]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_8,plain,
% 27.47/3.99      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 27.47/3.99      inference(cnf_transformation,[],[f76]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_935,plain,
% 27.47/3.99      ( k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 27.47/3.99      inference(cnf_transformation,[],[f74]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_7,plain,
% 27.47/3.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.47/3.99      inference(cnf_transformation,[],[f47]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_936,plain,
% 27.47/3.99      ( k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k2_zfmisc_1(k1_xboole_0,X1) ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_935,c_1,c_7]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_869,plain,
% 27.47/3.99      ( k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_870,plain,
% 27.47/3.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 27.47/3.99      inference(demodulation,[status(thm)],[c_869,c_1,c_7]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_937,plain,
% 27.47/3.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.47/3.99      inference(demodulation,[status(thm)],[c_936,c_1,c_7,c_870]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_10877,plain,
% 27.47/3.99      ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
% 27.47/3.99      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 27.47/3.99      inference(demodulation,[status(thm)],[c_10876,c_5,c_937]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_10914,plain,
% 27.47/3.99      ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
% 27.47/3.99      | v1_relat_1(sK0) != iProver_top
% 27.47/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_415,c_10877]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_12950,plain,
% 27.47/3.99      ( k5_relat_1(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_10914,c_20,c_38,c_51]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_13145,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(sK0,k1_xboole_0) ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_13136,c_12950]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_25510,plain,
% 27.47/3.99      ( k5_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) = k5_relat_1(sK0,k1_xboole_0) ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_25495,c_13145]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_50254,plain,
% 27.47/3.99      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_50242,c_25510]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_53902,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_53883,c_50254]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_53903,plain,
% 27.47/3.99      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 27.47/3.99      inference(demodulation,[status(thm)],[c_53902,c_5,c_870]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_54533,plain,
% 27.47/3.99      ( k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k1_xboole_0,sK0) ),
% 27.47/3.99      inference(demodulation,[status(thm)],[c_53903,c_1194]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2493,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)))))) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_2015,c_414]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_54808,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 27.47/3.99      inference(demodulation,[status(thm)],[c_54533,c_2493]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_7016,plain,
% 27.47/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_410,c_2918]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_54865,plain,
% 27.47/3.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_54808,c_7016]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_54866,plain,
% 27.47/3.99      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 27.47/3.99      inference(demodulation,[status(thm)],[c_54865,c_5,c_937]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_18,negated_conjecture,
% 27.47/3.99      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 27.47/3.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 27.47/3.99      inference(cnf_transformation,[],[f66]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_54536,plain,
% 27.47/3.99      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
% 27.47/3.99      | k1_xboole_0 != k1_xboole_0 ),
% 27.47/3.99      inference(demodulation,[status(thm)],[c_53903,c_18]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_54537,plain,
% 27.47/3.99      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
% 27.47/3.99      inference(equality_resolution_simp,[status(thm)],[c_54536]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(contradiction,plain,
% 27.47/3.99      ( $false ),
% 27.47/3.99      inference(minisat,[status(thm)],[c_54866,c_54537]) ).
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.47/3.99  
% 27.47/3.99  ------                               Statistics
% 27.47/3.99  
% 27.47/3.99  ------ General
% 27.47/3.99  
% 27.47/3.99  abstr_ref_over_cycles:                  0
% 27.47/3.99  abstr_ref_under_cycles:                 0
% 27.47/3.99  gc_basic_clause_elim:                   0
% 27.47/3.99  forced_gc_time:                         0
% 27.47/3.99  parsing_time:                           0.01
% 27.47/3.99  unif_index_cands_time:                  0.
% 27.47/3.99  unif_index_add_time:                    0.
% 27.47/3.99  orderings_time:                         0.
% 27.47/3.99  out_proof_time:                         0.014
% 27.47/3.99  total_time:                             3.181
% 27.47/3.99  num_of_symbols:                         43
% 27.47/3.99  num_of_terms:                           26373
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing
% 27.47/3.99  
% 27.47/3.99  num_of_splits:                          0
% 27.47/3.99  num_of_split_atoms:                     0
% 27.47/3.99  num_of_reused_defs:                     0
% 27.47/3.99  num_eq_ax_congr_red:                    0
% 27.47/3.99  num_of_sem_filtered_clauses:            1
% 27.47/3.99  num_of_subtypes:                        0
% 27.47/3.99  monotx_restored_types:                  0
% 27.47/3.99  sat_num_of_epr_types:                   0
% 27.47/3.99  sat_num_of_non_cyclic_types:            0
% 27.47/3.99  sat_guarded_non_collapsed_types:        0
% 27.47/3.99  num_pure_diseq_elim:                    0
% 27.47/3.99  simp_replaced_by:                       0
% 27.47/3.99  res_preprocessed:                       96
% 27.47/3.99  prep_upred:                             0
% 27.47/3.99  prep_unflattend:                        1
% 27.47/3.99  smt_new_axioms:                         0
% 27.47/3.99  pred_elim_cands:                        2
% 27.47/3.99  pred_elim:                              1
% 27.47/3.99  pred_elim_cl:                           1
% 27.47/3.99  pred_elim_cycles:                       3
% 27.47/3.99  merged_defs:                            0
% 27.47/3.99  merged_defs_ncl:                        0
% 27.47/3.99  bin_hyper_res:                          0
% 27.47/3.99  prep_cycles:                            4
% 27.47/3.99  pred_elim_time:                         0.
% 27.47/3.99  splitting_time:                         0.
% 27.47/3.99  sem_filter_time:                        0.
% 27.47/3.99  monotx_time:                            0.
% 27.47/3.99  subtype_inf_time:                       0.
% 27.47/3.99  
% 27.47/3.99  ------ Problem properties
% 27.47/3.99  
% 27.47/3.99  clauses:                                18
% 27.47/3.99  conjectures:                            2
% 27.47/3.99  epr:                                    5
% 27.47/3.99  horn:                                   18
% 27.47/3.99  ground:                                 5
% 27.47/3.99  unary:                                  11
% 27.47/3.99  binary:                                 2
% 27.47/3.99  lits:                                   32
% 27.47/3.99  lits_eq:                                13
% 27.47/3.99  fd_pure:                                0
% 27.47/3.99  fd_pseudo:                              0
% 27.47/3.99  fd_cond:                                0
% 27.47/3.99  fd_pseudo_cond:                         1
% 27.47/3.99  ac_symbols:                             0
% 27.47/3.99  
% 27.47/3.99  ------ Propositional Solver
% 27.47/3.99  
% 27.47/3.99  prop_solver_calls:                      36
% 27.47/3.99  prop_fast_solver_calls:                 1125
% 27.47/3.99  smt_solver_calls:                       0
% 27.47/3.99  smt_fast_solver_calls:                  0
% 27.47/3.99  prop_num_of_clauses:                    14715
% 27.47/3.99  prop_preprocess_simplified:             30342
% 27.47/3.99  prop_fo_subsumed:                       79
% 27.47/3.99  prop_solver_time:                       0.
% 27.47/3.99  smt_solver_time:                        0.
% 27.47/3.99  smt_fast_solver_time:                   0.
% 27.47/3.99  prop_fast_solver_time:                  0.
% 27.47/3.99  prop_unsat_core_time:                   0.001
% 27.47/3.99  
% 27.47/3.99  ------ QBF
% 27.47/3.99  
% 27.47/3.99  qbf_q_res:                              0
% 27.47/3.99  qbf_num_tautologies:                    0
% 27.47/3.99  qbf_prep_cycles:                        0
% 27.47/3.99  
% 27.47/3.99  ------ BMC1
% 27.47/3.99  
% 27.47/3.99  bmc1_current_bound:                     -1
% 27.47/3.99  bmc1_last_solved_bound:                 -1
% 27.47/3.99  bmc1_unsat_core_size:                   -1
% 27.47/3.99  bmc1_unsat_core_parents_size:           -1
% 27.47/3.99  bmc1_merge_next_fun:                    0
% 27.47/3.99  bmc1_unsat_core_clauses_time:           0.
% 27.47/3.99  
% 27.47/3.99  ------ Instantiation
% 27.47/3.99  
% 27.47/3.99  inst_num_of_clauses:                    4510
% 27.47/3.99  inst_num_in_passive:                    1674
% 27.47/3.99  inst_num_in_active:                     1177
% 27.47/3.99  inst_num_in_unprocessed:                1659
% 27.47/3.99  inst_num_of_loops:                      1640
% 27.47/3.99  inst_num_of_learning_restarts:          0
% 27.47/3.99  inst_num_moves_active_passive:          458
% 27.47/3.99  inst_lit_activity:                      0
% 27.47/3.99  inst_lit_activity_moves:                1
% 27.47/3.99  inst_num_tautologies:                   0
% 27.47/3.99  inst_num_prop_implied:                  0
% 27.47/3.99  inst_num_existing_simplified:           0
% 27.47/3.99  inst_num_eq_res_simplified:             0
% 27.47/3.99  inst_num_child_elim:                    0
% 27.47/3.99  inst_num_of_dismatching_blockings:      8838
% 27.47/3.99  inst_num_of_non_proper_insts:           10116
% 27.47/3.99  inst_num_of_duplicates:                 0
% 27.47/3.99  inst_inst_num_from_inst_to_res:         0
% 27.47/3.99  inst_dismatching_checking_time:         0.
% 27.47/3.99  
% 27.47/3.99  ------ Resolution
% 27.47/3.99  
% 27.47/3.99  res_num_of_clauses:                     0
% 27.47/3.99  res_num_in_passive:                     0
% 27.47/3.99  res_num_in_active:                      0
% 27.47/3.99  res_num_of_loops:                       100
% 27.47/3.99  res_forward_subset_subsumed:            1913
% 27.47/3.99  res_backward_subset_subsumed:           0
% 27.47/3.99  res_forward_subsumed:                   0
% 27.47/3.99  res_backward_subsumed:                  0
% 27.47/3.99  res_forward_subsumption_resolution:     0
% 27.47/3.99  res_backward_subsumption_resolution:    0
% 27.47/3.99  res_clause_to_clause_subsumption:       7468
% 27.47/3.99  res_orphan_elimination:                 0
% 27.47/3.99  res_tautology_del:                      733
% 27.47/3.99  res_num_eq_res_simplified:              0
% 27.47/3.99  res_num_sel_changes:                    0
% 27.47/3.99  res_moves_from_active_to_pass:          0
% 27.47/3.99  
% 27.47/3.99  ------ Superposition
% 27.47/3.99  
% 27.47/3.99  sup_time_total:                         0.
% 27.47/3.99  sup_time_generating:                    0.
% 27.47/3.99  sup_time_sim_full:                      0.
% 27.47/3.99  sup_time_sim_immed:                     0.
% 27.47/3.99  
% 27.47/3.99  sup_num_of_clauses:                     1399
% 27.47/3.99  sup_num_in_active:                      140
% 27.47/3.99  sup_num_in_passive:                     1259
% 27.47/3.99  sup_num_of_loops:                       327
% 27.47/3.99  sup_fw_superposition:                   1702
% 27.47/3.99  sup_bw_superposition:                   838
% 27.47/3.99  sup_immediate_simplified:               541
% 27.47/3.99  sup_given_eliminated:                   1
% 27.47/3.99  comparisons_done:                       0
% 27.47/3.99  comparisons_avoided:                    0
% 27.47/3.99  
% 27.47/3.99  ------ Simplifications
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  sim_fw_subset_subsumed:                 34
% 27.47/3.99  sim_bw_subset_subsumed:                 189
% 27.47/3.99  sim_fw_subsumed:                        45
% 27.47/3.99  sim_bw_subsumed:                        3
% 27.47/3.99  sim_fw_subsumption_res:                 0
% 27.47/3.99  sim_bw_subsumption_res:                 0
% 27.47/3.99  sim_tautology_del:                      5
% 27.47/3.99  sim_eq_tautology_del:                   128
% 27.47/3.99  sim_eq_res_simp:                        1
% 27.47/3.99  sim_fw_demodulated:                     161
% 27.47/3.99  sim_bw_demodulated:                     181
% 27.47/3.99  sim_light_normalised:                   387
% 27.47/3.99  sim_joinable_taut:                      0
% 27.47/3.99  sim_joinable_simp:                      0
% 27.47/3.99  sim_ac_normalised:                      0
% 27.47/3.99  sim_smt_subsumption:                    0
% 27.47/3.99  
%------------------------------------------------------------------------------
