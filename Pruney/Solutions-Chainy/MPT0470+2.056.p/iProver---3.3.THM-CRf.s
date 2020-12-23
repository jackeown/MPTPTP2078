%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:05 EST 2020

% Result     : Theorem 31.11s
% Output     : CNFRefutation 31.11s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 429 expanded)
%              Number of clauses        :   80 ( 119 expanded)
%              Number of leaves         :   28 ( 109 expanded)
%              Depth                    :   18
%              Number of atoms          :  340 ( 740 expanded)
%              Number of equality atoms :  185 ( 435 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f45])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f81])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f82])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f56,f83])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f83])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f40,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f47,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f47])).

fof(f76,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f71,f83])).

fof(f23,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f57,f83])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,
    ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_878,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_876,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_885,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_880,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2097,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_885,c_880])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_882,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4783,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_882])).

cnf(c_4869,plain,
    ( k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k1_xboole_0
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_876,c_4783])).

cnf(c_60734,plain,
    ( k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_xboole_0,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_878,c_4869])).

cnf(c_3,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_60990,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_60734,c_3])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_883,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_875,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1127,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_883,c_875])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_872,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_874,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_873,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1528,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_873])).

cnf(c_4300,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK2)),k2_relat_1(k5_relat_1(X0,sK2))))) = k5_relat_1(X0,sK2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_872,c_1528])).

cnf(c_4431,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK2)),k2_relat_1(k5_relat_1(k1_xboole_0,sK2))))) = k5_relat_1(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_1127,c_4300])).

cnf(c_18,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_205,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X1) != k1_xboole_0
    | k1_relat_1(X0) != X2
    | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_206,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X1) != k1_xboole_0
    | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_871,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_1380,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_871])).

cnf(c_19,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1381,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1380,c_19])).

cnf(c_35,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_37,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_57,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1515,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1381,c_37,c_57])).

cnf(c_1516,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1515])).

cnf(c_1519,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_872,c_1516])).

cnf(c_4433,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK2))))) = k5_relat_1(k1_xboole_0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4431,c_1519])).

cnf(c_61075,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k1_xboole_0)) = k5_relat_1(k1_xboole_0,sK2) ),
    inference(demodulation,[status(thm)],[c_60990,c_4433])).

cnf(c_8,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_61076,plain,
    ( k5_relat_1(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_61075,c_8])).

cnf(c_4301,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1528])).

cnf(c_47005,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK2,k1_xboole_0)),k2_relat_1(k5_relat_1(sK2,k1_xboole_0))))) = k5_relat_1(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_872,c_4301])).

cnf(c_17,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_223,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X0) != X2
    | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | k1_relat_1(X1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_224,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | k1_relat_1(X1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_870,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | k1_relat_1(X1) != k1_xboole_0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_1056,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_870])).

cnf(c_1057,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1056,c_18])).

cnf(c_1422,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1057,c_37,c_57])).

cnf(c_1423,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1422])).

cnf(c_1426,plain,
    ( k2_relat_1(k5_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_872,c_1423])).

cnf(c_47011,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK2,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK2,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_47005,c_1426])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_881,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1205,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_881])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_877,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2100,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_880])).

cnf(c_2591,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_885,c_2100])).

cnf(c_2673,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_2591])).

cnf(c_3046,plain,
    ( v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_2673])).

cnf(c_22350,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3046,c_882])).

cnf(c_47012,plain,
    ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_47011,c_8,c_22350])).

cnf(c_570,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_921,plain,
    ( k5_relat_1(k1_xboole_0,sK2) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_922,plain,
    ( k5_relat_1(k1_xboole_0,sK2) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_906,plain,
    ( k5_relat_1(sK2,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_907,plain,
    ( k5_relat_1(sK2,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_906])).

cnf(c_55,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61076,c_47012,c_922,c_907,c_2,c_55,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.11/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.11/4.50  
% 31.11/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.11/4.50  
% 31.11/4.50  ------  iProver source info
% 31.11/4.50  
% 31.11/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.11/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.11/4.50  git: non_committed_changes: false
% 31.11/4.50  git: last_make_outside_of_git: false
% 31.11/4.50  
% 31.11/4.50  ------ 
% 31.11/4.50  
% 31.11/4.50  ------ Input Options
% 31.11/4.50  
% 31.11/4.50  --out_options                           all
% 31.11/4.50  --tptp_safe_out                         true
% 31.11/4.50  --problem_path                          ""
% 31.11/4.50  --include_path                          ""
% 31.11/4.50  --clausifier                            res/vclausify_rel
% 31.11/4.50  --clausifier_options                    ""
% 31.11/4.50  --stdin                                 false
% 31.11/4.50  --stats_out                             all
% 31.11/4.50  
% 31.11/4.50  ------ General Options
% 31.11/4.50  
% 31.11/4.50  --fof                                   false
% 31.11/4.50  --time_out_real                         305.
% 31.11/4.50  --time_out_virtual                      -1.
% 31.11/4.50  --symbol_type_check                     false
% 31.11/4.50  --clausify_out                          false
% 31.11/4.50  --sig_cnt_out                           false
% 31.11/4.50  --trig_cnt_out                          false
% 31.11/4.50  --trig_cnt_out_tolerance                1.
% 31.11/4.50  --trig_cnt_out_sk_spl                   false
% 31.11/4.50  --abstr_cl_out                          false
% 31.11/4.50  
% 31.11/4.50  ------ Global Options
% 31.11/4.50  
% 31.11/4.50  --schedule                              default
% 31.11/4.50  --add_important_lit                     false
% 31.11/4.50  --prop_solver_per_cl                    1000
% 31.11/4.50  --min_unsat_core                        false
% 31.11/4.50  --soft_assumptions                      false
% 31.11/4.50  --soft_lemma_size                       3
% 31.11/4.50  --prop_impl_unit_size                   0
% 31.11/4.50  --prop_impl_unit                        []
% 31.11/4.50  --share_sel_clauses                     true
% 31.11/4.50  --reset_solvers                         false
% 31.11/4.50  --bc_imp_inh                            [conj_cone]
% 31.11/4.50  --conj_cone_tolerance                   3.
% 31.11/4.50  --extra_neg_conj                        none
% 31.11/4.50  --large_theory_mode                     true
% 31.11/4.50  --prolific_symb_bound                   200
% 31.11/4.50  --lt_threshold                          2000
% 31.11/4.50  --clause_weak_htbl                      true
% 31.11/4.50  --gc_record_bc_elim                     false
% 31.11/4.50  
% 31.11/4.50  ------ Preprocessing Options
% 31.11/4.50  
% 31.11/4.50  --preprocessing_flag                    true
% 31.11/4.50  --time_out_prep_mult                    0.1
% 31.11/4.50  --splitting_mode                        input
% 31.11/4.50  --splitting_grd                         true
% 31.11/4.50  --splitting_cvd                         false
% 31.11/4.50  --splitting_cvd_svl                     false
% 31.11/4.50  --splitting_nvd                         32
% 31.11/4.50  --sub_typing                            true
% 31.11/4.50  --prep_gs_sim                           true
% 31.11/4.50  --prep_unflatten                        true
% 31.11/4.50  --prep_res_sim                          true
% 31.11/4.50  --prep_upred                            true
% 31.11/4.50  --prep_sem_filter                       exhaustive
% 31.11/4.50  --prep_sem_filter_out                   false
% 31.11/4.50  --pred_elim                             true
% 31.11/4.50  --res_sim_input                         true
% 31.11/4.50  --eq_ax_congr_red                       true
% 31.11/4.50  --pure_diseq_elim                       true
% 31.11/4.50  --brand_transform                       false
% 31.11/4.50  --non_eq_to_eq                          false
% 31.11/4.50  --prep_def_merge                        true
% 31.11/4.50  --prep_def_merge_prop_impl              false
% 31.11/4.50  --prep_def_merge_mbd                    true
% 31.11/4.50  --prep_def_merge_tr_red                 false
% 31.11/4.50  --prep_def_merge_tr_cl                  false
% 31.11/4.50  --smt_preprocessing                     true
% 31.11/4.50  --smt_ac_axioms                         fast
% 31.11/4.50  --preprocessed_out                      false
% 31.11/4.50  --preprocessed_stats                    false
% 31.11/4.50  
% 31.11/4.50  ------ Abstraction refinement Options
% 31.11/4.50  
% 31.11/4.50  --abstr_ref                             []
% 31.11/4.50  --abstr_ref_prep                        false
% 31.11/4.50  --abstr_ref_until_sat                   false
% 31.11/4.50  --abstr_ref_sig_restrict                funpre
% 31.11/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.11/4.50  --abstr_ref_under                       []
% 31.11/4.50  
% 31.11/4.50  ------ SAT Options
% 31.11/4.50  
% 31.11/4.50  --sat_mode                              false
% 31.11/4.50  --sat_fm_restart_options                ""
% 31.11/4.50  --sat_gr_def                            false
% 31.11/4.50  --sat_epr_types                         true
% 31.11/4.50  --sat_non_cyclic_types                  false
% 31.11/4.50  --sat_finite_models                     false
% 31.11/4.50  --sat_fm_lemmas                         false
% 31.11/4.50  --sat_fm_prep                           false
% 31.11/4.50  --sat_fm_uc_incr                        true
% 31.11/4.50  --sat_out_model                         small
% 31.11/4.50  --sat_out_clauses                       false
% 31.11/4.50  
% 31.11/4.50  ------ QBF Options
% 31.11/4.50  
% 31.11/4.50  --qbf_mode                              false
% 31.11/4.50  --qbf_elim_univ                         false
% 31.11/4.50  --qbf_dom_inst                          none
% 31.11/4.50  --qbf_dom_pre_inst                      false
% 31.11/4.50  --qbf_sk_in                             false
% 31.11/4.50  --qbf_pred_elim                         true
% 31.11/4.50  --qbf_split                             512
% 31.11/4.50  
% 31.11/4.50  ------ BMC1 Options
% 31.11/4.50  
% 31.11/4.50  --bmc1_incremental                      false
% 31.11/4.50  --bmc1_axioms                           reachable_all
% 31.11/4.50  --bmc1_min_bound                        0
% 31.11/4.50  --bmc1_max_bound                        -1
% 31.11/4.50  --bmc1_max_bound_default                -1
% 31.11/4.50  --bmc1_symbol_reachability              true
% 31.11/4.50  --bmc1_property_lemmas                  false
% 31.11/4.50  --bmc1_k_induction                      false
% 31.11/4.50  --bmc1_non_equiv_states                 false
% 31.11/4.50  --bmc1_deadlock                         false
% 31.11/4.50  --bmc1_ucm                              false
% 31.11/4.50  --bmc1_add_unsat_core                   none
% 31.11/4.50  --bmc1_unsat_core_children              false
% 31.11/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.11/4.50  --bmc1_out_stat                         full
% 31.11/4.50  --bmc1_ground_init                      false
% 31.11/4.50  --bmc1_pre_inst_next_state              false
% 31.11/4.50  --bmc1_pre_inst_state                   false
% 31.11/4.50  --bmc1_pre_inst_reach_state             false
% 31.11/4.50  --bmc1_out_unsat_core                   false
% 31.11/4.50  --bmc1_aig_witness_out                  false
% 31.11/4.50  --bmc1_verbose                          false
% 31.11/4.50  --bmc1_dump_clauses_tptp                false
% 31.11/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.11/4.50  --bmc1_dump_file                        -
% 31.11/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.11/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.11/4.50  --bmc1_ucm_extend_mode                  1
% 31.11/4.50  --bmc1_ucm_init_mode                    2
% 31.11/4.50  --bmc1_ucm_cone_mode                    none
% 31.11/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.11/4.50  --bmc1_ucm_relax_model                  4
% 31.11/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.11/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.11/4.50  --bmc1_ucm_layered_model                none
% 31.11/4.50  --bmc1_ucm_max_lemma_size               10
% 31.11/4.50  
% 31.11/4.50  ------ AIG Options
% 31.11/4.50  
% 31.11/4.50  --aig_mode                              false
% 31.11/4.50  
% 31.11/4.50  ------ Instantiation Options
% 31.11/4.50  
% 31.11/4.50  --instantiation_flag                    true
% 31.11/4.50  --inst_sos_flag                         true
% 31.11/4.50  --inst_sos_phase                        true
% 31.11/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.11/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.11/4.50  --inst_lit_sel_side                     num_symb
% 31.11/4.50  --inst_solver_per_active                1400
% 31.11/4.50  --inst_solver_calls_frac                1.
% 31.11/4.50  --inst_passive_queue_type               priority_queues
% 31.11/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.11/4.50  --inst_passive_queues_freq              [25;2]
% 31.11/4.50  --inst_dismatching                      true
% 31.11/4.50  --inst_eager_unprocessed_to_passive     true
% 31.11/4.50  --inst_prop_sim_given                   true
% 31.11/4.50  --inst_prop_sim_new                     false
% 31.11/4.50  --inst_subs_new                         false
% 31.11/4.50  --inst_eq_res_simp                      false
% 31.11/4.50  --inst_subs_given                       false
% 31.11/4.50  --inst_orphan_elimination               true
% 31.11/4.50  --inst_learning_loop_flag               true
% 31.11/4.50  --inst_learning_start                   3000
% 31.11/4.50  --inst_learning_factor                  2
% 31.11/4.50  --inst_start_prop_sim_after_learn       3
% 31.11/4.50  --inst_sel_renew                        solver
% 31.11/4.50  --inst_lit_activity_flag                true
% 31.11/4.50  --inst_restr_to_given                   false
% 31.11/4.50  --inst_activity_threshold               500
% 31.11/4.50  --inst_out_proof                        true
% 31.11/4.50  
% 31.11/4.50  ------ Resolution Options
% 31.11/4.50  
% 31.11/4.50  --resolution_flag                       true
% 31.11/4.50  --res_lit_sel                           adaptive
% 31.11/4.50  --res_lit_sel_side                      none
% 31.11/4.50  --res_ordering                          kbo
% 31.11/4.50  --res_to_prop_solver                    active
% 31.11/4.50  --res_prop_simpl_new                    false
% 31.11/4.50  --res_prop_simpl_given                  true
% 31.11/4.50  --res_passive_queue_type                priority_queues
% 31.11/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.11/4.50  --res_passive_queues_freq               [15;5]
% 31.11/4.50  --res_forward_subs                      full
% 31.11/4.50  --res_backward_subs                     full
% 31.11/4.50  --res_forward_subs_resolution           true
% 31.11/4.50  --res_backward_subs_resolution          true
% 31.11/4.50  --res_orphan_elimination                true
% 31.11/4.50  --res_time_limit                        2.
% 31.11/4.50  --res_out_proof                         true
% 31.11/4.50  
% 31.11/4.50  ------ Superposition Options
% 31.11/4.50  
% 31.11/4.50  --superposition_flag                    true
% 31.11/4.50  --sup_passive_queue_type                priority_queues
% 31.11/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.11/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.11/4.50  --demod_completeness_check              fast
% 31.11/4.50  --demod_use_ground                      true
% 31.11/4.50  --sup_to_prop_solver                    passive
% 31.11/4.50  --sup_prop_simpl_new                    true
% 31.11/4.50  --sup_prop_simpl_given                  true
% 31.11/4.50  --sup_fun_splitting                     true
% 31.11/4.50  --sup_smt_interval                      50000
% 31.11/4.50  
% 31.11/4.50  ------ Superposition Simplification Setup
% 31.11/4.50  
% 31.11/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.11/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.11/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.11/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.11/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.11/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.11/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.11/4.50  --sup_immed_triv                        [TrivRules]
% 31.11/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.11/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.11/4.50  --sup_immed_bw_main                     []
% 31.11/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.11/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.11/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.11/4.50  --sup_input_bw                          []
% 31.11/4.50  
% 31.11/4.50  ------ Combination Options
% 31.11/4.50  
% 31.11/4.50  --comb_res_mult                         3
% 31.11/4.50  --comb_sup_mult                         2
% 31.11/4.50  --comb_inst_mult                        10
% 31.11/4.50  
% 31.11/4.50  ------ Debug Options
% 31.11/4.50  
% 31.11/4.50  --dbg_backtrace                         false
% 31.11/4.50  --dbg_dump_prop_clauses                 false
% 31.11/4.50  --dbg_dump_prop_clauses_file            -
% 31.11/4.50  --dbg_out_stat                          false
% 31.11/4.50  ------ Parsing...
% 31.11/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.11/4.50  
% 31.11/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.11/4.50  
% 31.11/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.11/4.50  
% 31.11/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.11/4.50  ------ Proving...
% 31.11/4.50  ------ Problem Properties 
% 31.11/4.50  
% 31.11/4.50  
% 31.11/4.50  clauses                                 21
% 31.11/4.50  conjectures                             2
% 31.11/4.50  EPR                                     7
% 31.11/4.50  Horn                                    19
% 31.11/4.50  unary                                   7
% 31.11/4.50  binary                                  11
% 31.11/4.50  lits                                    40
% 31.11/4.50  lits eq                                 12
% 31.11/4.50  fd_pure                                 0
% 31.11/4.50  fd_pseudo                               0
% 31.11/4.50  fd_cond                                 1
% 31.11/4.50  fd_pseudo_cond                          0
% 31.11/4.50  AC symbols                              0
% 31.11/4.50  
% 31.11/4.50  ------ Schedule dynamic 5 is on 
% 31.11/4.50  
% 31.11/4.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.11/4.50  
% 31.11/4.50  
% 31.11/4.50  ------ 
% 31.11/4.50  Current options:
% 31.11/4.50  ------ 
% 31.11/4.50  
% 31.11/4.50  ------ Input Options
% 31.11/4.50  
% 31.11/4.50  --out_options                           all
% 31.11/4.50  --tptp_safe_out                         true
% 31.11/4.50  --problem_path                          ""
% 31.11/4.50  --include_path                          ""
% 31.11/4.50  --clausifier                            res/vclausify_rel
% 31.11/4.50  --clausifier_options                    ""
% 31.11/4.50  --stdin                                 false
% 31.11/4.50  --stats_out                             all
% 31.11/4.50  
% 31.11/4.50  ------ General Options
% 31.11/4.50  
% 31.11/4.50  --fof                                   false
% 31.11/4.50  --time_out_real                         305.
% 31.11/4.50  --time_out_virtual                      -1.
% 31.11/4.50  --symbol_type_check                     false
% 31.11/4.50  --clausify_out                          false
% 31.11/4.50  --sig_cnt_out                           false
% 31.11/4.50  --trig_cnt_out                          false
% 31.11/4.50  --trig_cnt_out_tolerance                1.
% 31.11/4.50  --trig_cnt_out_sk_spl                   false
% 31.11/4.50  --abstr_cl_out                          false
% 31.11/4.50  
% 31.11/4.50  ------ Global Options
% 31.11/4.50  
% 31.11/4.50  --schedule                              default
% 31.11/4.50  --add_important_lit                     false
% 31.11/4.50  --prop_solver_per_cl                    1000
% 31.11/4.50  --min_unsat_core                        false
% 31.11/4.50  --soft_assumptions                      false
% 31.11/4.50  --soft_lemma_size                       3
% 31.11/4.50  --prop_impl_unit_size                   0
% 31.11/4.50  --prop_impl_unit                        []
% 31.11/4.50  --share_sel_clauses                     true
% 31.11/4.50  --reset_solvers                         false
% 31.11/4.50  --bc_imp_inh                            [conj_cone]
% 31.11/4.50  --conj_cone_tolerance                   3.
% 31.11/4.50  --extra_neg_conj                        none
% 31.11/4.50  --large_theory_mode                     true
% 31.11/4.50  --prolific_symb_bound                   200
% 31.11/4.50  --lt_threshold                          2000
% 31.11/4.50  --clause_weak_htbl                      true
% 31.11/4.50  --gc_record_bc_elim                     false
% 31.11/4.50  
% 31.11/4.50  ------ Preprocessing Options
% 31.11/4.50  
% 31.11/4.50  --preprocessing_flag                    true
% 31.11/4.50  --time_out_prep_mult                    0.1
% 31.11/4.50  --splitting_mode                        input
% 31.11/4.50  --splitting_grd                         true
% 31.11/4.50  --splitting_cvd                         false
% 31.11/4.50  --splitting_cvd_svl                     false
% 31.11/4.50  --splitting_nvd                         32
% 31.11/4.50  --sub_typing                            true
% 31.11/4.50  --prep_gs_sim                           true
% 31.11/4.50  --prep_unflatten                        true
% 31.11/4.50  --prep_res_sim                          true
% 31.11/4.50  --prep_upred                            true
% 31.11/4.50  --prep_sem_filter                       exhaustive
% 31.11/4.50  --prep_sem_filter_out                   false
% 31.11/4.50  --pred_elim                             true
% 31.11/4.50  --res_sim_input                         true
% 31.11/4.50  --eq_ax_congr_red                       true
% 31.11/4.50  --pure_diseq_elim                       true
% 31.11/4.50  --brand_transform                       false
% 31.11/4.50  --non_eq_to_eq                          false
% 31.11/4.50  --prep_def_merge                        true
% 31.11/4.50  --prep_def_merge_prop_impl              false
% 31.11/4.50  --prep_def_merge_mbd                    true
% 31.11/4.50  --prep_def_merge_tr_red                 false
% 31.11/4.50  --prep_def_merge_tr_cl                  false
% 31.11/4.50  --smt_preprocessing                     true
% 31.11/4.50  --smt_ac_axioms                         fast
% 31.11/4.50  --preprocessed_out                      false
% 31.11/4.50  --preprocessed_stats                    false
% 31.11/4.50  
% 31.11/4.50  ------ Abstraction refinement Options
% 31.11/4.50  
% 31.11/4.50  --abstr_ref                             []
% 31.11/4.50  --abstr_ref_prep                        false
% 31.11/4.50  --abstr_ref_until_sat                   false
% 31.11/4.50  --abstr_ref_sig_restrict                funpre
% 31.11/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.11/4.50  --abstr_ref_under                       []
% 31.11/4.50  
% 31.11/4.50  ------ SAT Options
% 31.11/4.50  
% 31.11/4.50  --sat_mode                              false
% 31.11/4.50  --sat_fm_restart_options                ""
% 31.11/4.50  --sat_gr_def                            false
% 31.11/4.50  --sat_epr_types                         true
% 31.11/4.50  --sat_non_cyclic_types                  false
% 31.11/4.50  --sat_finite_models                     false
% 31.11/4.50  --sat_fm_lemmas                         false
% 31.11/4.50  --sat_fm_prep                           false
% 31.11/4.50  --sat_fm_uc_incr                        true
% 31.11/4.50  --sat_out_model                         small
% 31.11/4.50  --sat_out_clauses                       false
% 31.11/4.50  
% 31.11/4.50  ------ QBF Options
% 31.11/4.50  
% 31.11/4.50  --qbf_mode                              false
% 31.11/4.50  --qbf_elim_univ                         false
% 31.11/4.50  --qbf_dom_inst                          none
% 31.11/4.50  --qbf_dom_pre_inst                      false
% 31.11/4.50  --qbf_sk_in                             false
% 31.11/4.50  --qbf_pred_elim                         true
% 31.11/4.50  --qbf_split                             512
% 31.11/4.50  
% 31.11/4.50  ------ BMC1 Options
% 31.11/4.50  
% 31.11/4.50  --bmc1_incremental                      false
% 31.11/4.50  --bmc1_axioms                           reachable_all
% 31.11/4.50  --bmc1_min_bound                        0
% 31.11/4.50  --bmc1_max_bound                        -1
% 31.11/4.50  --bmc1_max_bound_default                -1
% 31.11/4.50  --bmc1_symbol_reachability              true
% 31.11/4.50  --bmc1_property_lemmas                  false
% 31.11/4.50  --bmc1_k_induction                      false
% 31.11/4.50  --bmc1_non_equiv_states                 false
% 31.11/4.50  --bmc1_deadlock                         false
% 31.11/4.50  --bmc1_ucm                              false
% 31.11/4.50  --bmc1_add_unsat_core                   none
% 31.11/4.50  --bmc1_unsat_core_children              false
% 31.11/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.11/4.50  --bmc1_out_stat                         full
% 31.11/4.50  --bmc1_ground_init                      false
% 31.11/4.50  --bmc1_pre_inst_next_state              false
% 31.11/4.50  --bmc1_pre_inst_state                   false
% 31.11/4.50  --bmc1_pre_inst_reach_state             false
% 31.11/4.50  --bmc1_out_unsat_core                   false
% 31.11/4.50  --bmc1_aig_witness_out                  false
% 31.11/4.50  --bmc1_verbose                          false
% 31.11/4.50  --bmc1_dump_clauses_tptp                false
% 31.11/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.11/4.50  --bmc1_dump_file                        -
% 31.11/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.11/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.11/4.50  --bmc1_ucm_extend_mode                  1
% 31.11/4.50  --bmc1_ucm_init_mode                    2
% 31.11/4.50  --bmc1_ucm_cone_mode                    none
% 31.11/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.11/4.50  --bmc1_ucm_relax_model                  4
% 31.11/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.11/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.11/4.50  --bmc1_ucm_layered_model                none
% 31.11/4.50  --bmc1_ucm_max_lemma_size               10
% 31.11/4.50  
% 31.11/4.50  ------ AIG Options
% 31.11/4.50  
% 31.11/4.50  --aig_mode                              false
% 31.11/4.50  
% 31.11/4.50  ------ Instantiation Options
% 31.11/4.50  
% 31.11/4.50  --instantiation_flag                    true
% 31.11/4.50  --inst_sos_flag                         true
% 31.11/4.50  --inst_sos_phase                        true
% 31.11/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.11/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.11/4.50  --inst_lit_sel_side                     none
% 31.11/4.50  --inst_solver_per_active                1400
% 31.11/4.50  --inst_solver_calls_frac                1.
% 31.11/4.50  --inst_passive_queue_type               priority_queues
% 31.11/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.11/4.50  --inst_passive_queues_freq              [25;2]
% 31.11/4.50  --inst_dismatching                      true
% 31.11/4.50  --inst_eager_unprocessed_to_passive     true
% 31.11/4.50  --inst_prop_sim_given                   true
% 31.11/4.50  --inst_prop_sim_new                     false
% 31.11/4.50  --inst_subs_new                         false
% 31.11/4.50  --inst_eq_res_simp                      false
% 31.11/4.50  --inst_subs_given                       false
% 31.11/4.50  --inst_orphan_elimination               true
% 31.11/4.50  --inst_learning_loop_flag               true
% 31.11/4.50  --inst_learning_start                   3000
% 31.11/4.50  --inst_learning_factor                  2
% 31.11/4.50  --inst_start_prop_sim_after_learn       3
% 31.11/4.50  --inst_sel_renew                        solver
% 31.11/4.50  --inst_lit_activity_flag                true
% 31.11/4.50  --inst_restr_to_given                   false
% 31.11/4.50  --inst_activity_threshold               500
% 31.11/4.50  --inst_out_proof                        true
% 31.11/4.50  
% 31.11/4.50  ------ Resolution Options
% 31.11/4.50  
% 31.11/4.50  --resolution_flag                       false
% 31.11/4.50  --res_lit_sel                           adaptive
% 31.11/4.50  --res_lit_sel_side                      none
% 31.11/4.50  --res_ordering                          kbo
% 31.11/4.50  --res_to_prop_solver                    active
% 31.11/4.50  --res_prop_simpl_new                    false
% 31.11/4.50  --res_prop_simpl_given                  true
% 31.11/4.50  --res_passive_queue_type                priority_queues
% 31.11/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.11/4.50  --res_passive_queues_freq               [15;5]
% 31.11/4.50  --res_forward_subs                      full
% 31.11/4.50  --res_backward_subs                     full
% 31.11/4.50  --res_forward_subs_resolution           true
% 31.11/4.50  --res_backward_subs_resolution          true
% 31.11/4.50  --res_orphan_elimination                true
% 31.11/4.50  --res_time_limit                        2.
% 31.11/4.50  --res_out_proof                         true
% 31.11/4.50  
% 31.11/4.50  ------ Superposition Options
% 31.11/4.50  
% 31.11/4.50  --superposition_flag                    true
% 31.11/4.50  --sup_passive_queue_type                priority_queues
% 31.11/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.11/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.11/4.50  --demod_completeness_check              fast
% 31.11/4.50  --demod_use_ground                      true
% 31.11/4.50  --sup_to_prop_solver                    passive
% 31.11/4.50  --sup_prop_simpl_new                    true
% 31.11/4.50  --sup_prop_simpl_given                  true
% 31.11/4.50  --sup_fun_splitting                     true
% 31.11/4.50  --sup_smt_interval                      50000
% 31.11/4.50  
% 31.11/4.50  ------ Superposition Simplification Setup
% 31.11/4.50  
% 31.11/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.11/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.11/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.11/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.11/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.11/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.11/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.11/4.50  --sup_immed_triv                        [TrivRules]
% 31.11/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.11/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.11/4.50  --sup_immed_bw_main                     []
% 31.11/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.11/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.11/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.11/4.50  --sup_input_bw                          []
% 31.11/4.50  
% 31.11/4.50  ------ Combination Options
% 31.11/4.50  
% 31.11/4.50  --comb_res_mult                         3
% 31.11/4.50  --comb_sup_mult                         2
% 31.11/4.50  --comb_inst_mult                        10
% 31.11/4.50  
% 31.11/4.50  ------ Debug Options
% 31.11/4.50  
% 31.11/4.50  --dbg_backtrace                         false
% 31.11/4.50  --dbg_dump_prop_clauses                 false
% 31.11/4.50  --dbg_dump_prop_clauses_file            -
% 31.11/4.50  --dbg_out_stat                          false
% 31.11/4.50  
% 31.11/4.50  
% 31.11/4.50  
% 31.11/4.50  
% 31.11/4.50  ------ Proving...
% 31.11/4.50  
% 31.11/4.50  
% 31.11/4.50  % SZS status Theorem for theBenchmark.p
% 31.11/4.50  
% 31.11/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.11/4.50  
% 31.11/4.50  fof(f9,axiom,(
% 31.11/4.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f59,plain,(
% 31.11/4.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f9])).
% 31.11/4.50  
% 31.11/4.50  fof(f16,axiom,(
% 31.11/4.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f31,plain,(
% 31.11/4.50    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 31.11/4.50    inference(ennf_transformation,[],[f16])).
% 31.11/4.50  
% 31.11/4.50  fof(f66,plain,(
% 31.11/4.50    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f31])).
% 31.11/4.50  
% 31.11/4.50  fof(f1,axiom,(
% 31.11/4.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f41,plain,(
% 31.11/4.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 31.11/4.50    inference(nnf_transformation,[],[f1])).
% 31.11/4.50  
% 31.11/4.50  fof(f42,plain,(
% 31.11/4.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 31.11/4.50    inference(rectify,[],[f41])).
% 31.11/4.50  
% 31.11/4.50  fof(f43,plain,(
% 31.11/4.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 31.11/4.50    introduced(choice_axiom,[])).
% 31.11/4.50  
% 31.11/4.50  fof(f44,plain,(
% 31.11/4.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 31.11/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 31.11/4.50  
% 31.11/4.50  fof(f50,plain,(
% 31.11/4.50    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f44])).
% 31.11/4.50  
% 31.11/4.50  fof(f6,axiom,(
% 31.11/4.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f27,plain,(
% 31.11/4.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 31.11/4.50    inference(rectify,[],[f6])).
% 31.11/4.50  
% 31.11/4.50  fof(f30,plain,(
% 31.11/4.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 31.11/4.50    inference(ennf_transformation,[],[f27])).
% 31.11/4.50  
% 31.11/4.50  fof(f45,plain,(
% 31.11/4.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 31.11/4.50    introduced(choice_axiom,[])).
% 31.11/4.50  
% 31.11/4.50  fof(f46,plain,(
% 31.11/4.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 31.11/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f45])).
% 31.11/4.50  
% 31.11/4.50  fof(f56,plain,(
% 31.11/4.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 31.11/4.50    inference(cnf_transformation,[],[f46])).
% 31.11/4.50  
% 31.11/4.50  fof(f17,axiom,(
% 31.11/4.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f68,plain,(
% 31.11/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 31.11/4.50    inference(cnf_transformation,[],[f17])).
% 31.11/4.50  
% 31.11/4.50  fof(f10,axiom,(
% 31.11/4.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f60,plain,(
% 31.11/4.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f10])).
% 31.11/4.50  
% 31.11/4.50  fof(f11,axiom,(
% 31.11/4.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f61,plain,(
% 31.11/4.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f11])).
% 31.11/4.50  
% 31.11/4.50  fof(f12,axiom,(
% 31.11/4.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f62,plain,(
% 31.11/4.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f12])).
% 31.11/4.50  
% 31.11/4.50  fof(f13,axiom,(
% 31.11/4.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f63,plain,(
% 31.11/4.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f13])).
% 31.11/4.50  
% 31.11/4.50  fof(f14,axiom,(
% 31.11/4.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f64,plain,(
% 31.11/4.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f14])).
% 31.11/4.50  
% 31.11/4.50  fof(f15,axiom,(
% 31.11/4.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f65,plain,(
% 31.11/4.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f15])).
% 31.11/4.50  
% 31.11/4.50  fof(f78,plain,(
% 31.11/4.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 31.11/4.50    inference(definition_unfolding,[],[f64,f65])).
% 31.11/4.50  
% 31.11/4.50  fof(f79,plain,(
% 31.11/4.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 31.11/4.50    inference(definition_unfolding,[],[f63,f78])).
% 31.11/4.50  
% 31.11/4.50  fof(f80,plain,(
% 31.11/4.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 31.11/4.50    inference(definition_unfolding,[],[f62,f79])).
% 31.11/4.50  
% 31.11/4.50  fof(f81,plain,(
% 31.11/4.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 31.11/4.50    inference(definition_unfolding,[],[f61,f80])).
% 31.11/4.50  
% 31.11/4.50  fof(f82,plain,(
% 31.11/4.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 31.11/4.50    inference(definition_unfolding,[],[f60,f81])).
% 31.11/4.50  
% 31.11/4.50  fof(f83,plain,(
% 31.11/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 31.11/4.50    inference(definition_unfolding,[],[f68,f82])).
% 31.11/4.50  
% 31.11/4.50  fof(f85,plain,(
% 31.11/4.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 31.11/4.50    inference(definition_unfolding,[],[f56,f83])).
% 31.11/4.50  
% 31.11/4.50  fof(f4,axiom,(
% 31.11/4.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f28,plain,(
% 31.11/4.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 31.11/4.50    inference(ennf_transformation,[],[f4])).
% 31.11/4.50  
% 31.11/4.50  fof(f53,plain,(
% 31.11/4.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f28])).
% 31.11/4.50  
% 31.11/4.50  fof(f3,axiom,(
% 31.11/4.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f26,plain,(
% 31.11/4.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 31.11/4.50    inference(rectify,[],[f3])).
% 31.11/4.50  
% 31.11/4.50  fof(f52,plain,(
% 31.11/4.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 31.11/4.50    inference(cnf_transformation,[],[f26])).
% 31.11/4.50  
% 31.11/4.50  fof(f84,plain,(
% 31.11/4.50    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 31.11/4.50    inference(definition_unfolding,[],[f52,f83])).
% 31.11/4.50  
% 31.11/4.50  fof(f2,axiom,(
% 31.11/4.50    v1_xboole_0(k1_xboole_0)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f51,plain,(
% 31.11/4.50    v1_xboole_0(k1_xboole_0)),
% 31.11/4.50    inference(cnf_transformation,[],[f2])).
% 31.11/4.50  
% 31.11/4.50  fof(f18,axiom,(
% 31.11/4.50    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f32,plain,(
% 31.11/4.50    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 31.11/4.50    inference(ennf_transformation,[],[f18])).
% 31.11/4.50  
% 31.11/4.50  fof(f69,plain,(
% 31.11/4.50    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f32])).
% 31.11/4.50  
% 31.11/4.50  fof(f24,conjecture,(
% 31.11/4.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f25,negated_conjecture,(
% 31.11/4.50    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 31.11/4.50    inference(negated_conjecture,[],[f24])).
% 31.11/4.50  
% 31.11/4.50  fof(f40,plain,(
% 31.11/4.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 31.11/4.50    inference(ennf_transformation,[],[f25])).
% 31.11/4.50  
% 31.11/4.50  fof(f47,plain,(
% 31.11/4.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)) & v1_relat_1(sK2))),
% 31.11/4.50    introduced(choice_axiom,[])).
% 31.11/4.50  
% 31.11/4.50  fof(f48,plain,(
% 31.11/4.50    (k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)) & v1_relat_1(sK2)),
% 31.11/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f47])).
% 31.11/4.50  
% 31.11/4.50  fof(f76,plain,(
% 31.11/4.50    v1_relat_1(sK2)),
% 31.11/4.50    inference(cnf_transformation,[],[f48])).
% 31.11/4.50  
% 31.11/4.50  fof(f19,axiom,(
% 31.11/4.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f33,plain,(
% 31.11/4.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 31.11/4.50    inference(ennf_transformation,[],[f19])).
% 31.11/4.50  
% 31.11/4.50  fof(f34,plain,(
% 31.11/4.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 31.11/4.50    inference(flattening,[],[f33])).
% 31.11/4.50  
% 31.11/4.50  fof(f70,plain,(
% 31.11/4.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f34])).
% 31.11/4.50  
% 31.11/4.50  fof(f20,axiom,(
% 31.11/4.50    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f35,plain,(
% 31.11/4.50    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 31.11/4.50    inference(ennf_transformation,[],[f20])).
% 31.11/4.50  
% 31.11/4.50  fof(f71,plain,(
% 31.11/4.50    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f35])).
% 31.11/4.50  
% 31.11/4.50  fof(f88,plain,(
% 31.11/4.50    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 31.11/4.50    inference(definition_unfolding,[],[f71,f83])).
% 31.11/4.50  
% 31.11/4.50  fof(f23,axiom,(
% 31.11/4.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f75,plain,(
% 31.11/4.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 31.11/4.50    inference(cnf_transformation,[],[f23])).
% 31.11/4.50  
% 31.11/4.50  fof(f8,axiom,(
% 31.11/4.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f58,plain,(
% 31.11/4.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f8])).
% 31.11/4.50  
% 31.11/4.50  fof(f21,axiom,(
% 31.11/4.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f36,plain,(
% 31.11/4.50    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.11/4.50    inference(ennf_transformation,[],[f21])).
% 31.11/4.50  
% 31.11/4.50  fof(f37,plain,(
% 31.11/4.50    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.11/4.50    inference(flattening,[],[f36])).
% 31.11/4.50  
% 31.11/4.50  fof(f72,plain,(
% 31.11/4.50    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f37])).
% 31.11/4.50  
% 31.11/4.50  fof(f74,plain,(
% 31.11/4.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 31.11/4.50    inference(cnf_transformation,[],[f23])).
% 31.11/4.50  
% 31.11/4.50  fof(f7,axiom,(
% 31.11/4.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f57,plain,(
% 31.11/4.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f7])).
% 31.11/4.50  
% 31.11/4.50  fof(f87,plain,(
% 31.11/4.50    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 31.11/4.50    inference(definition_unfolding,[],[f57,f83])).
% 31.11/4.50  
% 31.11/4.50  fof(f22,axiom,(
% 31.11/4.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f38,plain,(
% 31.11/4.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.11/4.50    inference(ennf_transformation,[],[f22])).
% 31.11/4.50  
% 31.11/4.50  fof(f39,plain,(
% 31.11/4.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.11/4.50    inference(flattening,[],[f38])).
% 31.11/4.50  
% 31.11/4.50  fof(f73,plain,(
% 31.11/4.50    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f39])).
% 31.11/4.50  
% 31.11/4.50  fof(f5,axiom,(
% 31.11/4.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 31.11/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.11/4.50  
% 31.11/4.50  fof(f29,plain,(
% 31.11/4.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 31.11/4.50    inference(ennf_transformation,[],[f5])).
% 31.11/4.50  
% 31.11/4.50  fof(f54,plain,(
% 31.11/4.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f29])).
% 31.11/4.50  
% 31.11/4.50  fof(f67,plain,(
% 31.11/4.50    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 31.11/4.50    inference(cnf_transformation,[],[f31])).
% 31.11/4.50  
% 31.11/4.50  fof(f77,plain,(
% 31.11/4.50    k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)),
% 31.11/4.50    inference(cnf_transformation,[],[f48])).
% 31.11/4.50  
% 31.11/4.50  cnf(c_10,plain,
% 31.11/4.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 31.11/4.50      inference(cnf_transformation,[],[f59]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_878,plain,
% 31.11/4.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_12,plain,
% 31.11/4.50      ( ~ r1_xboole_0(X0,X1)
% 31.11/4.50      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 31.11/4.50      inference(cnf_transformation,[],[f66]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_876,plain,
% 31.11/4.50      ( r1_xboole_0(X0,X1) != iProver_top
% 31.11/4.50      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_0,plain,
% 31.11/4.50      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 31.11/4.50      inference(cnf_transformation,[],[f50]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_885,plain,
% 31.11/4.50      ( r2_hidden(sK0(X0),X0) = iProver_top
% 31.11/4.50      | v1_xboole_0(X0) = iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_6,plain,
% 31.11/4.50      ( ~ r1_xboole_0(X0,X1)
% 31.11/4.50      | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 31.11/4.50      inference(cnf_transformation,[],[f85]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_880,plain,
% 31.11/4.50      ( r1_xboole_0(X0,X1) != iProver_top
% 31.11/4.50      | r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_2097,plain,
% 31.11/4.50      ( r1_xboole_0(X0,X1) != iProver_top
% 31.11/4.50      | v1_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_885,c_880]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_4,plain,
% 31.11/4.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 31.11/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_882,plain,
% 31.11/4.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_4783,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_xboole_0
% 31.11/4.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_2097,c_882]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_4869,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k1_xboole_0
% 31.11/4.50      | r1_xboole_0(X0,X2) != iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_876,c_4783]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_60734,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_xboole_0,X2))) = k1_xboole_0 ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_878,c_4869]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_3,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 31.11/4.50      inference(cnf_transformation,[],[f84]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_60990,plain,
% 31.11/4.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_60734,c_3]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_2,plain,
% 31.11/4.50      ( v1_xboole_0(k1_xboole_0) ),
% 31.11/4.50      inference(cnf_transformation,[],[f51]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_883,plain,
% 31.11/4.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_13,plain,
% 31.11/4.50      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 31.11/4.50      inference(cnf_transformation,[],[f69]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_875,plain,
% 31.11/4.50      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1127,plain,
% 31.11/4.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_883,c_875]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_21,negated_conjecture,
% 31.11/4.50      ( v1_relat_1(sK2) ),
% 31.11/4.50      inference(cnf_transformation,[],[f76]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_872,plain,
% 31.11/4.50      ( v1_relat_1(sK2) = iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_14,plain,
% 31.11/4.50      ( ~ v1_relat_1(X0)
% 31.11/4.50      | ~ v1_relat_1(X1)
% 31.11/4.50      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 31.11/4.50      inference(cnf_transformation,[],[f70]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_874,plain,
% 31.11/4.50      ( v1_relat_1(X0) != iProver_top
% 31.11/4.50      | v1_relat_1(X1) != iProver_top
% 31.11/4.50      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_15,plain,
% 31.11/4.50      ( ~ v1_relat_1(X0)
% 31.11/4.50      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 31.11/4.50      inference(cnf_transformation,[],[f88]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_873,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 31.11/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1528,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 31.11/4.50      | v1_relat_1(X1) != iProver_top
% 31.11/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_874,c_873]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_4300,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK2)),k2_relat_1(k5_relat_1(X0,sK2))))) = k5_relat_1(X0,sK2)
% 31.11/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_872,c_1528]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_4431,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK2)),k2_relat_1(k5_relat_1(k1_xboole_0,sK2))))) = k5_relat_1(k1_xboole_0,sK2) ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_1127,c_4300]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_18,plain,
% 31.11/4.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 31.11/4.50      inference(cnf_transformation,[],[f75]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_9,plain,
% 31.11/4.50      ( r1_tarski(k1_xboole_0,X0) ),
% 31.11/4.50      inference(cnf_transformation,[],[f58]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_16,plain,
% 31.11/4.50      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 31.11/4.50      | ~ v1_relat_1(X1)
% 31.11/4.50      | ~ v1_relat_1(X0)
% 31.11/4.50      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 31.11/4.50      inference(cnf_transformation,[],[f72]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_205,plain,
% 31.11/4.50      ( ~ v1_relat_1(X0)
% 31.11/4.50      | ~ v1_relat_1(X1)
% 31.11/4.50      | k2_relat_1(X1) != k1_xboole_0
% 31.11/4.50      | k1_relat_1(X0) != X2
% 31.11/4.50      | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) ),
% 31.11/4.50      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_206,plain,
% 31.11/4.50      ( ~ v1_relat_1(X0)
% 31.11/4.50      | ~ v1_relat_1(X1)
% 31.11/4.50      | k2_relat_1(X1) != k1_xboole_0
% 31.11/4.50      | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) ),
% 31.11/4.50      inference(unflattening,[status(thm)],[c_205]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_871,plain,
% 31.11/4.50      ( k2_relat_1(X0) != k1_xboole_0
% 31.11/4.50      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 31.11/4.50      | v1_relat_1(X0) != iProver_top
% 31.11/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_206]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1380,plain,
% 31.11/4.50      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 31.11/4.50      | v1_relat_1(X0) != iProver_top
% 31.11/4.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_18,c_871]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_19,plain,
% 31.11/4.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 31.11/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1381,plain,
% 31.11/4.50      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 31.11/4.50      | v1_relat_1(X0) != iProver_top
% 31.11/4.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.11/4.50      inference(light_normalisation,[status(thm)],[c_1380,c_19]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_35,plain,
% 31.11/4.50      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_37,plain,
% 31.11/4.50      ( v1_relat_1(k1_xboole_0) = iProver_top
% 31.11/4.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 31.11/4.50      inference(instantiation,[status(thm)],[c_35]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_57,plain,
% 31.11/4.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1515,plain,
% 31.11/4.50      ( v1_relat_1(X0) != iProver_top
% 31.11/4.50      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 31.11/4.50      inference(global_propositional_subsumption,
% 31.11/4.50                [status(thm)],
% 31.11/4.50                [c_1381,c_37,c_57]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1516,plain,
% 31.11/4.50      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 31.11/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.11/4.50      inference(renaming,[status(thm)],[c_1515]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1519,plain,
% 31.11/4.50      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK2)) = k1_xboole_0 ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_872,c_1516]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_4433,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK2))))) = k5_relat_1(k1_xboole_0,sK2) ),
% 31.11/4.50      inference(light_normalisation,[status(thm)],[c_4431,c_1519]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_61075,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k1_xboole_0)) = k5_relat_1(k1_xboole_0,sK2) ),
% 31.11/4.50      inference(demodulation,[status(thm)],[c_60990,c_4433]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_8,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 31.11/4.50      inference(cnf_transformation,[],[f87]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_61076,plain,
% 31.11/4.50      ( k5_relat_1(k1_xboole_0,sK2) = k1_xboole_0 ),
% 31.11/4.50      inference(demodulation,[status(thm)],[c_61075,c_8]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_4301,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
% 31.11/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_1127,c_1528]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_47005,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK2,k1_xboole_0)),k2_relat_1(k5_relat_1(sK2,k1_xboole_0))))) = k5_relat_1(sK2,k1_xboole_0) ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_872,c_4301]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_17,plain,
% 31.11/4.50      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 31.11/4.50      | ~ v1_relat_1(X1)
% 31.11/4.50      | ~ v1_relat_1(X0)
% 31.11/4.50      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 31.11/4.50      inference(cnf_transformation,[],[f73]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_223,plain,
% 31.11/4.50      ( ~ v1_relat_1(X0)
% 31.11/4.50      | ~ v1_relat_1(X1)
% 31.11/4.50      | k2_relat_1(X0) != X2
% 31.11/4.50      | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 31.11/4.50      | k1_relat_1(X1) != k1_xboole_0 ),
% 31.11/4.50      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_224,plain,
% 31.11/4.50      ( ~ v1_relat_1(X0)
% 31.11/4.50      | ~ v1_relat_1(X1)
% 31.11/4.50      | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 31.11/4.50      | k1_relat_1(X1) != k1_xboole_0 ),
% 31.11/4.50      inference(unflattening,[status(thm)],[c_223]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_870,plain,
% 31.11/4.50      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 31.11/4.50      | k1_relat_1(X1) != k1_xboole_0
% 31.11/4.50      | v1_relat_1(X1) != iProver_top
% 31.11/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1056,plain,
% 31.11/4.50      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 31.11/4.50      | v1_relat_1(X0) != iProver_top
% 31.11/4.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_19,c_870]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1057,plain,
% 31.11/4.50      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 31.11/4.50      | v1_relat_1(X0) != iProver_top
% 31.11/4.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.11/4.50      inference(light_normalisation,[status(thm)],[c_1056,c_18]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1422,plain,
% 31.11/4.50      ( v1_relat_1(X0) != iProver_top
% 31.11/4.50      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 31.11/4.50      inference(global_propositional_subsumption,
% 31.11/4.50                [status(thm)],
% 31.11/4.50                [c_1057,c_37,c_57]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1423,plain,
% 31.11/4.50      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 31.11/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.11/4.50      inference(renaming,[status(thm)],[c_1422]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1426,plain,
% 31.11/4.50      ( k2_relat_1(k5_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_872,c_1423]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_47011,plain,
% 31.11/4.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK2,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK2,k1_xboole_0) ),
% 31.11/4.50      inference(light_normalisation,[status(thm)],[c_47005,c_1426]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_5,plain,
% 31.11/4.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 31.11/4.50      inference(cnf_transformation,[],[f54]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_881,plain,
% 31.11/4.50      ( r1_xboole_0(X0,X1) != iProver_top
% 31.11/4.50      | r1_xboole_0(X1,X0) = iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_1205,plain,
% 31.11/4.50      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_878,c_881]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_11,plain,
% 31.11/4.50      ( ~ r1_xboole_0(X0,X1)
% 31.11/4.50      | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 31.11/4.50      inference(cnf_transformation,[],[f67]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_877,plain,
% 31.11/4.50      ( r1_xboole_0(X0,X1) != iProver_top
% 31.11/4.50      | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 31.11/4.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_2100,plain,
% 31.11/4.50      ( r1_xboole_0(X0,X0) != iProver_top
% 31.11/4.50      | r2_hidden(X1,X0) != iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_3,c_880]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_2591,plain,
% 31.11/4.50      ( r1_xboole_0(X0,X0) != iProver_top
% 31.11/4.50      | v1_xboole_0(X0) = iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_885,c_2100]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_2673,plain,
% 31.11/4.50      ( r1_xboole_0(X0,X0) != iProver_top
% 31.11/4.50      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_877,c_2591]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_3046,plain,
% 31.11/4.50      ( v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_1205,c_2673]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_22350,plain,
% 31.11/4.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 31.11/4.50      inference(superposition,[status(thm)],[c_3046,c_882]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_47012,plain,
% 31.11/4.50      ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 31.11/4.50      inference(demodulation,[status(thm)],[c_47011,c_8,c_22350]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_570,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_921,plain,
% 31.11/4.50      ( k5_relat_1(k1_xboole_0,sK2) != X0
% 31.11/4.50      | k1_xboole_0 != X0
% 31.11/4.50      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2) ),
% 31.11/4.50      inference(instantiation,[status(thm)],[c_570]) ).
% 31.11/4.50  
% 31.11/4.50  cnf(c_922,plain,
% 31.11/4.50      ( k5_relat_1(k1_xboole_0,sK2) != k1_xboole_0
% 31.11/4.51      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2)
% 31.11/4.51      | k1_xboole_0 != k1_xboole_0 ),
% 31.11/4.51      inference(instantiation,[status(thm)],[c_921]) ).
% 31.11/4.51  
% 31.11/4.51  cnf(c_906,plain,
% 31.11/4.51      ( k5_relat_1(sK2,k1_xboole_0) != X0
% 31.11/4.51      | k1_xboole_0 != X0
% 31.11/4.51      | k1_xboole_0 = k5_relat_1(sK2,k1_xboole_0) ),
% 31.11/4.51      inference(instantiation,[status(thm)],[c_570]) ).
% 31.11/4.51  
% 31.11/4.51  cnf(c_907,plain,
% 31.11/4.51      ( k5_relat_1(sK2,k1_xboole_0) != k1_xboole_0
% 31.11/4.51      | k1_xboole_0 = k5_relat_1(sK2,k1_xboole_0)
% 31.11/4.51      | k1_xboole_0 != k1_xboole_0 ),
% 31.11/4.51      inference(instantiation,[status(thm)],[c_906]) ).
% 31.11/4.51  
% 31.11/4.51  cnf(c_55,plain,
% 31.11/4.51      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 31.11/4.51      inference(instantiation,[status(thm)],[c_4]) ).
% 31.11/4.51  
% 31.11/4.51  cnf(c_20,negated_conjecture,
% 31.11/4.51      ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
% 31.11/4.51      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
% 31.11/4.51      inference(cnf_transformation,[],[f77]) ).
% 31.11/4.51  
% 31.11/4.51  cnf(contradiction,plain,
% 31.11/4.51      ( $false ),
% 31.11/4.51      inference(minisat,
% 31.11/4.51                [status(thm)],
% 31.11/4.51                [c_61076,c_47012,c_922,c_907,c_2,c_55,c_20]) ).
% 31.11/4.51  
% 31.11/4.51  
% 31.11/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.11/4.51  
% 31.11/4.51  ------                               Statistics
% 31.11/4.51  
% 31.11/4.51  ------ General
% 31.11/4.51  
% 31.11/4.51  abstr_ref_over_cycles:                  0
% 31.11/4.51  abstr_ref_under_cycles:                 0
% 31.11/4.51  gc_basic_clause_elim:                   0
% 31.11/4.51  forced_gc_time:                         0
% 31.11/4.51  parsing_time:                           0.009
% 31.11/4.51  unif_index_cands_time:                  0.
% 31.11/4.51  unif_index_add_time:                    0.
% 31.11/4.51  orderings_time:                         0.
% 31.11/4.51  out_proof_time:                         0.011
% 31.11/4.51  total_time:                             3.631
% 31.11/4.51  num_of_symbols:                         46
% 31.11/4.51  num_of_terms:                           33189
% 31.11/4.51  
% 31.11/4.51  ------ Preprocessing
% 31.11/4.51  
% 31.11/4.51  num_of_splits:                          0
% 31.11/4.51  num_of_split_atoms:                     0
% 31.11/4.51  num_of_reused_defs:                     0
% 31.11/4.51  num_eq_ax_congr_red:                    30
% 31.11/4.51  num_of_sem_filtered_clauses:            1
% 31.11/4.51  num_of_subtypes:                        0
% 31.11/4.51  monotx_restored_types:                  0
% 31.11/4.51  sat_num_of_epr_types:                   0
% 31.11/4.51  sat_num_of_non_cyclic_types:            0
% 31.11/4.51  sat_guarded_non_collapsed_types:        0
% 31.11/4.51  num_pure_diseq_elim:                    0
% 31.11/4.51  simp_replaced_by:                       0
% 31.11/4.51  res_preprocessed:                       110
% 31.11/4.51  prep_upred:                             0
% 31.11/4.51  prep_unflattend:                        24
% 31.11/4.51  smt_new_axioms:                         0
% 31.11/4.51  pred_elim_cands:                        4
% 31.11/4.51  pred_elim:                              1
% 31.11/4.51  pred_elim_cl:                           1
% 31.11/4.51  pred_elim_cycles:                       5
% 31.11/4.51  merged_defs:                            0
% 31.11/4.51  merged_defs_ncl:                        0
% 31.11/4.51  bin_hyper_res:                          0
% 31.11/4.51  prep_cycles:                            4
% 31.11/4.51  pred_elim_time:                         0.004
% 31.11/4.51  splitting_time:                         0.
% 31.11/4.51  sem_filter_time:                        0.
% 31.11/4.51  monotx_time:                            0.001
% 31.11/4.51  subtype_inf_time:                       0.
% 31.11/4.51  
% 31.11/4.51  ------ Problem properties
% 31.11/4.51  
% 31.11/4.51  clauses:                                21
% 31.11/4.51  conjectures:                            2
% 31.11/4.51  epr:                                    7
% 31.11/4.51  horn:                                   19
% 31.11/4.51  ground:                                 5
% 31.11/4.51  unary:                                  7
% 31.11/4.51  binary:                                 11
% 31.11/4.51  lits:                                   40
% 31.11/4.51  lits_eq:                                12
% 31.11/4.51  fd_pure:                                0
% 31.11/4.51  fd_pseudo:                              0
% 31.11/4.51  fd_cond:                                1
% 31.11/4.51  fd_pseudo_cond:                         0
% 31.11/4.51  ac_symbols:                             0
% 31.11/4.51  
% 31.11/4.51  ------ Propositional Solver
% 31.11/4.51  
% 31.11/4.51  prop_solver_calls:                      51
% 31.11/4.51  prop_fast_solver_calls:                 2011
% 31.11/4.51  smt_solver_calls:                       0
% 31.11/4.51  smt_fast_solver_calls:                  0
% 31.11/4.51  prop_num_of_clauses:                    16826
% 31.11/4.51  prop_preprocess_simplified:             34494
% 31.11/4.51  prop_fo_subsumed:                       12
% 31.11/4.51  prop_solver_time:                       0.
% 31.11/4.51  smt_solver_time:                        0.
% 31.11/4.51  smt_fast_solver_time:                   0.
% 31.11/4.51  prop_fast_solver_time:                  0.
% 31.11/4.51  prop_unsat_core_time:                   0.002
% 31.11/4.51  
% 31.11/4.51  ------ QBF
% 31.11/4.51  
% 31.11/4.51  qbf_q_res:                              0
% 31.11/4.51  qbf_num_tautologies:                    0
% 31.11/4.51  qbf_prep_cycles:                        0
% 31.11/4.51  
% 31.11/4.51  ------ BMC1
% 31.11/4.51  
% 31.11/4.51  bmc1_current_bound:                     -1
% 31.11/4.51  bmc1_last_solved_bound:                 -1
% 31.11/4.51  bmc1_unsat_core_size:                   -1
% 31.11/4.51  bmc1_unsat_core_parents_size:           -1
% 31.11/4.51  bmc1_merge_next_fun:                    0
% 31.11/4.51  bmc1_unsat_core_clauses_time:           0.
% 31.11/4.51  
% 31.11/4.51  ------ Instantiation
% 31.11/4.51  
% 31.11/4.51  inst_num_of_clauses:                    1931
% 31.11/4.51  inst_num_in_passive:                    580
% 31.11/4.51  inst_num_in_active:                     2727
% 31.11/4.51  inst_num_in_unprocessed:                544
% 31.11/4.51  inst_num_of_loops:                      3839
% 31.11/4.51  inst_num_of_learning_restarts:          1
% 31.11/4.51  inst_num_moves_active_passive:          1099
% 31.11/4.51  inst_lit_activity:                      0
% 31.11/4.51  inst_lit_activity_moves:                0
% 31.11/4.51  inst_num_tautologies:                   0
% 31.11/4.51  inst_num_prop_implied:                  0
% 31.11/4.51  inst_num_existing_simplified:           0
% 31.11/4.51  inst_num_eq_res_simplified:             0
% 31.11/4.51  inst_num_child_elim:                    0
% 31.11/4.51  inst_num_of_dismatching_blockings:      7988
% 31.11/4.51  inst_num_of_non_proper_insts:           10846
% 31.11/4.51  inst_num_of_duplicates:                 0
% 31.11/4.51  inst_inst_num_from_inst_to_res:         0
% 31.11/4.51  inst_dismatching_checking_time:         0.
% 31.11/4.51  
% 31.11/4.51  ------ Resolution
% 31.11/4.51  
% 31.11/4.51  res_num_of_clauses:                     33
% 31.11/4.51  res_num_in_passive:                     33
% 31.11/4.51  res_num_in_active:                      0
% 31.11/4.51  res_num_of_loops:                       114
% 31.11/4.51  res_forward_subset_subsumed:            791
% 31.11/4.51  res_backward_subset_subsumed:           2
% 31.11/4.51  res_forward_subsumed:                   0
% 31.11/4.51  res_backward_subsumed:                  0
% 31.11/4.51  res_forward_subsumption_resolution:     0
% 31.11/4.51  res_backward_subsumption_resolution:    0
% 31.11/4.51  res_clause_to_clause_subsumption:       10898
% 31.11/4.51  res_orphan_elimination:                 0
% 31.11/4.51  res_tautology_del:                      1560
% 31.11/4.51  res_num_eq_res_simplified:              0
% 31.11/4.51  res_num_sel_changes:                    0
% 31.11/4.51  res_moves_from_active_to_pass:          0
% 31.11/4.51  
% 31.11/4.51  ------ Superposition
% 31.11/4.51  
% 31.11/4.51  sup_time_total:                         0.
% 31.11/4.51  sup_time_generating:                    0.
% 31.11/4.51  sup_time_sim_full:                      0.
% 31.11/4.51  sup_time_sim_immed:                     0.
% 31.11/4.51  
% 31.11/4.51  sup_num_of_clauses:                     1812
% 31.11/4.51  sup_num_in_active:                      555
% 31.11/4.51  sup_num_in_passive:                     1257
% 31.11/4.51  sup_num_of_loops:                       766
% 31.11/4.51  sup_fw_superposition:                   2143
% 31.11/4.51  sup_bw_superposition:                   506
% 31.11/4.51  sup_immediate_simplified:               580
% 31.11/4.51  sup_given_eliminated:                   2
% 31.11/4.51  comparisons_done:                       0
% 31.11/4.51  comparisons_avoided:                    0
% 31.11/4.51  
% 31.11/4.51  ------ Simplifications
% 31.11/4.51  
% 31.11/4.51  
% 31.11/4.51  sim_fw_subset_subsumed:                 79
% 31.11/4.51  sim_bw_subset_subsumed:                 6
% 31.11/4.51  sim_fw_subsumed:                        33
% 31.11/4.51  sim_bw_subsumed:                        0
% 31.11/4.51  sim_fw_subsumption_res:                 0
% 31.11/4.51  sim_bw_subsumption_res:                 0
% 31.11/4.51  sim_tautology_del:                      11
% 31.11/4.51  sim_eq_tautology_del:                   326
% 31.11/4.51  sim_eq_res_simp:                        6
% 31.11/4.51  sim_fw_demodulated:                     60
% 31.11/4.51  sim_bw_demodulated:                     211
% 31.11/4.51  sim_light_normalised:                   446
% 31.11/4.51  sim_joinable_taut:                      0
% 31.11/4.51  sim_joinable_simp:                      0
% 31.11/4.51  sim_ac_normalised:                      0
% 31.11/4.51  sim_smt_subsumption:                    0
% 31.11/4.51  
%------------------------------------------------------------------------------
