%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:12 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 493 expanded)
%              Number of clauses        :   69 ( 120 expanded)
%              Number of leaves         :   22 ( 121 expanded)
%              Depth                    :   19
%              Number of atoms          :  326 ( 968 expanded)
%              Number of equality atoms :  202 ( 680 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f64])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f166,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f101])).

fof(f38,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f38])).

fof(f60,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f78,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f60,f78])).

fof(f134,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f79])).

fof(f28,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f122,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f120,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f165,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f102])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f136,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f97,f98])).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f96,f136])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f95,f137])).

fof(f139,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f94,f138])).

fof(f140,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f93,f139])).

fof(f141,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f113,f140])).

fof(f142,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f86,f141])).

fof(f147,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f84,f142])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f151,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f90,f142])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f83,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f135,plain,
    ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
    inference(cnf_transformation,[],[f79])).

fof(f37,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f132,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f133,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f123,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f32,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_31,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1377,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f166])).

cnf(c_45,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1366,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_32,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1376,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_41,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1367,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_1754,plain,
    ( k5_relat_1(sK5,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK5,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_1367])).

cnf(c_2295,plain,
    ( k5_relat_1(k5_relat_1(sK5,k2_zfmisc_1(X0,X1)),X2) = k5_relat_1(sK5,k5_relat_1(k2_zfmisc_1(X0,X1),X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1376,c_1754])).

cnf(c_2463,plain,
    ( k5_relat_1(sK5,k5_relat_1(k2_zfmisc_1(X0,X1),sK5)) = k5_relat_1(k5_relat_1(sK5,k2_zfmisc_1(X0,X1)),sK5) ),
    inference(superposition,[status(thm)],[c_1366,c_2295])).

cnf(c_9667,plain,
    ( v1_relat_1(k5_relat_1(sK5,k5_relat_1(k2_zfmisc_1(X0,X1),sK5))) = iProver_top
    | v1_relat_1(k5_relat_1(sK5,k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2463,c_1377])).

cnf(c_46,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_10851,plain,
    ( v1_relat_1(k5_relat_1(sK5,k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k5_relat_1(sK5,k5_relat_1(k2_zfmisc_1(X0,X1),sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9667,c_46])).

cnf(c_10852,plain,
    ( v1_relat_1(k5_relat_1(sK5,k5_relat_1(k2_zfmisc_1(X0,X1),sK5))) = iProver_top
    | v1_relat_1(k5_relat_1(sK5,k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10851])).

cnf(c_10860,plain,
    ( v1_relat_1(k5_relat_1(sK5,k5_relat_1(k1_xboole_0,sK5))) = iProver_top
    | v1_relat_1(k5_relat_1(sK5,k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_10852])).

cnf(c_10931,plain,
    ( v1_relat_1(k5_relat_1(sK5,k5_relat_1(k1_xboole_0,sK5))) = iProver_top
    | v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10860,c_12])).

cnf(c_30,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1378,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4241,plain,
    ( k5_relat_1(k5_relat_1(sK5,k4_relat_1(X0)),X1) = k5_relat_1(sK5,k5_relat_1(k4_relat_1(X0),X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1378,c_1754])).

cnf(c_4607,plain,
    ( k5_relat_1(sK5,k5_relat_1(k4_relat_1(sK5),X0)) = k5_relat_1(k5_relat_1(sK5,k4_relat_1(sK5)),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_4241])).

cnf(c_12257,plain,
    ( k5_relat_1(k5_relat_1(sK5,k4_relat_1(sK5)),k5_relat_1(sK5,k5_relat_1(k1_xboole_0,sK5))) = k5_relat_1(sK5,k5_relat_1(k4_relat_1(sK5),k5_relat_1(sK5,k5_relat_1(k1_xboole_0,sK5))))
    | v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10931,c_4607])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f165])).

cnf(c_2292,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1376])).

cnf(c_5837,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_5838,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5837])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f147])).

cnf(c_9,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f151])).

cnf(c_7216,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_5,c_9])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_44,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2489,plain,
    ( ~ r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_relat_1(sK5,k1_xboole_0))
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
    inference(resolution,[status(thm)],[c_1,c_44])).

cnf(c_2501,plain,
    ( ~ r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_relat_1(sK5,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK5)) ),
    inference(resolution,[status(thm)],[c_2489,c_1])).

cnf(c_1820,plain,
    ( r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK5))
    | k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,sK5)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2234,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,sK5)))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2504,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_relat_1(sK5,k1_xboole_0))
    | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0)
    | ~ r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2501,c_1820,c_2234])).

cnf(c_2505,plain,
    ( ~ r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_relat_1(sK5,k1_xboole_0)) ),
    inference(renaming,[status(thm)],[c_2504])).

cnf(c_7429,plain,
    ( ~ r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7216,c_2505])).

cnf(c_7432,plain,
    ( r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7429])).

cnf(c_43,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_38,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1370,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5460,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_43,c_1370])).

cnf(c_42,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_5474,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5460,c_42])).

cnf(c_15338,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5474,c_2292])).

cnf(c_15339,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15338])).

cnf(c_1388,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10262,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1388])).

cnf(c_15345,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15339,c_10262])).

cnf(c_15352,plain,
    ( k2_relat_1(k5_relat_1(sK5,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1366,c_15345])).

cnf(c_33,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1375,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_15430,plain,
    ( r1_tarski(k5_relat_1(sK5,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK5,k1_xboole_0)),k1_xboole_0)) = iProver_top
    | v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15352,c_1375])).

cnf(c_15451,plain,
    ( r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15430,c_11])).

cnf(c_37,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1371,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6888,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_42,c_1371])).

cnf(c_6920,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6888,c_43])).

cnf(c_17852,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6920,c_2292])).

cnf(c_17853,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17852])).

cnf(c_17859,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17853,c_10262])).

cnf(c_17866,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1366,c_17859])).

cnf(c_18118,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK5),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK5)))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17866,c_1375])).

cnf(c_18139,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18118,c_12])).

cnf(c_20450,plain,
    ( v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12257,c_46,c_2292,c_5838,c_7432,c_15451,c_18139])).

cnf(c_20455,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_20450])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20455,c_2292,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:29:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.65/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.50  
% 7.65/1.50  ------  iProver source info
% 7.65/1.50  
% 7.65/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.50  git: non_committed_changes: false
% 7.65/1.50  git: last_make_outside_of_git: false
% 7.65/1.50  
% 7.65/1.50  ------ 
% 7.65/1.50  ------ Parsing...
% 7.65/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.50  ------ Proving...
% 7.65/1.50  ------ Problem Properties 
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  clauses                                 45
% 7.65/1.50  conjectures                             2
% 7.65/1.50  EPR                                     3
% 7.65/1.50  Horn                                    40
% 7.65/1.50  unary                                   19
% 7.65/1.50  binary                                  13
% 7.65/1.50  lits                                    94
% 7.65/1.50  lits eq                                 40
% 7.65/1.50  fd_pure                                 0
% 7.65/1.50  fd_pseudo                               0
% 7.65/1.50  fd_cond                                 1
% 7.65/1.50  fd_pseudo_cond                          2
% 7.65/1.50  AC symbols                              0
% 7.65/1.50  
% 7.65/1.50  ------ Input Options Time Limit: Unbounded
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  ------ 
% 7.65/1.50  Current options:
% 7.65/1.50  ------ 
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  ------ Proving...
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS status Theorem for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  fof(f27,axiom,(
% 7.65/1.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f46,plain,(
% 7.65/1.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f47,plain,(
% 7.65/1.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f46])).
% 7.65/1.50  
% 7.65/1.50  fof(f121,plain,(
% 7.65/1.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f47])).
% 7.65/1.50  
% 7.65/1.50  fof(f18,axiom,(
% 7.65/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f64,plain,(
% 7.65/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.65/1.50    inference(nnf_transformation,[],[f18])).
% 7.65/1.50  
% 7.65/1.50  fof(f65,plain,(
% 7.65/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.65/1.50    inference(flattening,[],[f64])).
% 7.65/1.50  
% 7.65/1.50  fof(f101,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.65/1.50    inference(cnf_transformation,[],[f65])).
% 7.65/1.50  
% 7.65/1.50  fof(f166,plain,(
% 7.65/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.65/1.50    inference(equality_resolution,[],[f101])).
% 7.65/1.50  
% 7.65/1.50  fof(f38,conjecture,(
% 7.65/1.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f39,negated_conjecture,(
% 7.65/1.50    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 7.65/1.50    inference(negated_conjecture,[],[f38])).
% 7.65/1.50  
% 7.65/1.50  fof(f60,plain,(
% 7.65/1.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f39])).
% 7.65/1.50  
% 7.65/1.50  fof(f78,plain,(
% 7.65/1.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5)) & v1_relat_1(sK5))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f79,plain,(
% 7.65/1.50    (k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5)) & v1_relat_1(sK5)),
% 7.65/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f60,f78])).
% 7.65/1.50  
% 7.65/1.50  fof(f134,plain,(
% 7.65/1.50    v1_relat_1(sK5)),
% 7.65/1.50    inference(cnf_transformation,[],[f79])).
% 7.65/1.50  
% 7.65/1.50  fof(f28,axiom,(
% 7.65/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f122,plain,(
% 7.65/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f28])).
% 7.65/1.50  
% 7.65/1.50  fof(f36,axiom,(
% 7.65/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f59,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f36])).
% 7.65/1.50  
% 7.65/1.50  fof(f131,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f59])).
% 7.65/1.50  
% 7.65/1.50  fof(f26,axiom,(
% 7.65/1.50    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f45,plain,(
% 7.65/1.50    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f120,plain,(
% 7.65/1.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f45])).
% 7.65/1.50  
% 7.65/1.50  fof(f102,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.65/1.50    inference(cnf_transformation,[],[f65])).
% 7.65/1.50  
% 7.65/1.50  fof(f165,plain,(
% 7.65/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.65/1.50    inference(equality_resolution,[],[f102])).
% 7.65/1.50  
% 7.65/1.50  fof(f3,axiom,(
% 7.65/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f63,plain,(
% 7.65/1.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.65/1.50    inference(nnf_transformation,[],[f3])).
% 7.65/1.50  
% 7.65/1.50  fof(f84,plain,(
% 7.65/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.65/1.50    inference(cnf_transformation,[],[f63])).
% 7.65/1.50  
% 7.65/1.50  fof(f4,axiom,(
% 7.65/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f86,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f4])).
% 7.65/1.50  
% 7.65/1.50  fof(f23,axiom,(
% 7.65/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f113,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f23])).
% 7.65/1.50  
% 7.65/1.50  fof(f11,axiom,(
% 7.65/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f93,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f11])).
% 7.65/1.50  
% 7.65/1.50  fof(f12,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f94,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f12])).
% 7.65/1.50  
% 7.65/1.50  fof(f13,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f95,plain,(
% 7.65/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f13])).
% 7.65/1.50  
% 7.65/1.50  fof(f14,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f96,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f14])).
% 7.65/1.50  
% 7.65/1.50  fof(f15,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f97,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f15])).
% 7.65/1.50  
% 7.65/1.50  fof(f16,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f98,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f16])).
% 7.65/1.50  
% 7.65/1.50  fof(f136,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f97,f98])).
% 7.65/1.50  
% 7.65/1.50  fof(f137,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f96,f136])).
% 7.65/1.50  
% 7.65/1.50  fof(f138,plain,(
% 7.65/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f95,f137])).
% 7.65/1.50  
% 7.65/1.50  fof(f139,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f94,f138])).
% 7.65/1.50  
% 7.65/1.50  fof(f140,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f93,f139])).
% 7.65/1.50  
% 7.65/1.50  fof(f141,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.65/1.50    inference(definition_unfolding,[],[f113,f140])).
% 7.65/1.50  
% 7.65/1.50  fof(f142,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.65/1.50    inference(definition_unfolding,[],[f86,f141])).
% 7.65/1.50  
% 7.65/1.50  fof(f147,plain,(
% 7.65/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.65/1.50    inference(definition_unfolding,[],[f84,f142])).
% 7.65/1.50  
% 7.65/1.50  fof(f8,axiom,(
% 7.65/1.50    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f90,plain,(
% 7.65/1.50    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.65/1.50    inference(cnf_transformation,[],[f8])).
% 7.65/1.50  
% 7.65/1.50  fof(f151,plain,(
% 7.65/1.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 7.65/1.50    inference(definition_unfolding,[],[f90,f142])).
% 7.65/1.50  
% 7.65/1.50  fof(f2,axiom,(
% 7.65/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f61,plain,(
% 7.65/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.65/1.50    inference(nnf_transformation,[],[f2])).
% 7.65/1.50  
% 7.65/1.50  fof(f62,plain,(
% 7.65/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.65/1.50    inference(flattening,[],[f61])).
% 7.65/1.50  
% 7.65/1.50  fof(f83,plain,(
% 7.65/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f62])).
% 7.65/1.50  
% 7.65/1.50  fof(f135,plain,(
% 7.65/1.50    k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5)),
% 7.65/1.50    inference(cnf_transformation,[],[f79])).
% 7.65/1.50  
% 7.65/1.50  fof(f37,axiom,(
% 7.65/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f132,plain,(
% 7.65/1.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.65/1.50    inference(cnf_transformation,[],[f37])).
% 7.65/1.50  
% 7.65/1.50  fof(f33,axiom,(
% 7.65/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f53,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f33])).
% 7.65/1.50  
% 7.65/1.50  fof(f54,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f53])).
% 7.65/1.50  
% 7.65/1.50  fof(f128,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f54])).
% 7.65/1.50  
% 7.65/1.50  fof(f133,plain,(
% 7.65/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.65/1.50    inference(cnf_transformation,[],[f37])).
% 7.65/1.50  
% 7.65/1.50  fof(f29,axiom,(
% 7.65/1.50    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f48,plain,(
% 7.65/1.50    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f29])).
% 7.65/1.50  
% 7.65/1.50  fof(f123,plain,(
% 7.65/1.50    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f48])).
% 7.65/1.50  
% 7.65/1.50  fof(f32,axiom,(
% 7.65/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f51,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f32])).
% 7.65/1.50  
% 7.65/1.50  fof(f52,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f51])).
% 7.65/1.50  
% 7.65/1.50  fof(f127,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f52])).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31,plain,
% 7.65/1.50      ( ~ v1_relat_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f121]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1377,plain,
% 7.65/1.50      ( v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top
% 7.65/1.50      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12,plain,
% 7.65/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f166]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_45,negated_conjecture,
% 7.65/1.50      ( v1_relat_1(sK5) ),
% 7.65/1.50      inference(cnf_transformation,[],[f134]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1366,plain,
% 7.65/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_32,plain,
% 7.65/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f122]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1376,plain,
% 7.65/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_41,plain,
% 7.65/1.50      ( ~ v1_relat_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | ~ v1_relat_1(X2)
% 7.65/1.50      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f131]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1367,plain,
% 7.65/1.50      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.65/1.50      | v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top
% 7.65/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1754,plain,
% 7.65/1.50      ( k5_relat_1(sK5,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK5,X0),X1)
% 7.65/1.50      | v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1366,c_1367]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2295,plain,
% 7.65/1.50      ( k5_relat_1(k5_relat_1(sK5,k2_zfmisc_1(X0,X1)),X2) = k5_relat_1(sK5,k5_relat_1(k2_zfmisc_1(X0,X1),X2))
% 7.65/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1376,c_1754]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2463,plain,
% 7.65/1.50      ( k5_relat_1(sK5,k5_relat_1(k2_zfmisc_1(X0,X1),sK5)) = k5_relat_1(k5_relat_1(sK5,k2_zfmisc_1(X0,X1)),sK5) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1366,c_2295]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9667,plain,
% 7.65/1.50      ( v1_relat_1(k5_relat_1(sK5,k5_relat_1(k2_zfmisc_1(X0,X1),sK5))) = iProver_top
% 7.65/1.50      | v1_relat_1(k5_relat_1(sK5,k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2463,c_1377]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_46,plain,
% 7.65/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10851,plain,
% 7.65/1.50      ( v1_relat_1(k5_relat_1(sK5,k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | v1_relat_1(k5_relat_1(sK5,k5_relat_1(k2_zfmisc_1(X0,X1),sK5))) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_9667,c_46]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10852,plain,
% 7.65/1.50      ( v1_relat_1(k5_relat_1(sK5,k5_relat_1(k2_zfmisc_1(X0,X1),sK5))) = iProver_top
% 7.65/1.50      | v1_relat_1(k5_relat_1(sK5,k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_10851]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10860,plain,
% 7.65/1.50      ( v1_relat_1(k5_relat_1(sK5,k5_relat_1(k1_xboole_0,sK5))) = iProver_top
% 7.65/1.50      | v1_relat_1(k5_relat_1(sK5,k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_12,c_10852]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10931,plain,
% 7.65/1.50      ( v1_relat_1(k5_relat_1(sK5,k5_relat_1(k1_xboole_0,sK5))) = iProver_top
% 7.65/1.50      | v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_10860,c_12]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_30,plain,
% 7.65/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f120]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1378,plain,
% 7.65/1.50      ( v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4241,plain,
% 7.65/1.50      ( k5_relat_1(k5_relat_1(sK5,k4_relat_1(X0)),X1) = k5_relat_1(sK5,k5_relat_1(k4_relat_1(X0),X1))
% 7.65/1.50      | v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1378,c_1754]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4607,plain,
% 7.65/1.50      ( k5_relat_1(sK5,k5_relat_1(k4_relat_1(sK5),X0)) = k5_relat_1(k5_relat_1(sK5,k4_relat_1(sK5)),X0)
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1366,c_4241]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12257,plain,
% 7.65/1.50      ( k5_relat_1(k5_relat_1(sK5,k4_relat_1(sK5)),k5_relat_1(sK5,k5_relat_1(k1_xboole_0,sK5))) = k5_relat_1(sK5,k5_relat_1(k4_relat_1(sK5),k5_relat_1(sK5,k5_relat_1(k1_xboole_0,sK5))))
% 7.65/1.50      | v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_10931,c_4607]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11,plain,
% 7.65/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f165]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2292,plain,
% 7.65/1.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_11,c_1376]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5837,plain,
% 7.65/1.50      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK5))
% 7.65/1.50      | ~ v1_relat_1(sK5)
% 7.65/1.50      | ~ v1_relat_1(k1_xboole_0) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_31]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5838,plain,
% 7.65/1.50      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK5)) = iProver_top
% 7.65/1.50      | v1_relat_1(sK5) != iProver_top
% 7.65/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_5837]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5,plain,
% 7.65/1.50      ( r1_tarski(X0,X1)
% 7.65/1.50      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f147]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9,plain,
% 7.65/1.50      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f151]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7216,plain,
% 7.65/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.65/1.50      inference(resolution,[status(thm)],[c_5,c_9]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.65/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_44,negated_conjecture,
% 7.65/1.50      ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
% 7.65/1.50      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
% 7.65/1.50      inference(cnf_transformation,[],[f135]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2489,plain,
% 7.65/1.50      ( ~ r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0)
% 7.65/1.50      | ~ r1_tarski(k1_xboole_0,k5_relat_1(sK5,k1_xboole_0))
% 7.65/1.50      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
% 7.65/1.50      inference(resolution,[status(thm)],[c_1,c_44]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2501,plain,
% 7.65/1.50      ( ~ r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0)
% 7.65/1.50      | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0)
% 7.65/1.50      | ~ r1_tarski(k1_xboole_0,k5_relat_1(sK5,k1_xboole_0))
% 7.65/1.50      | ~ r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK5)) ),
% 7.65/1.50      inference(resolution,[status(thm)],[c_2489,c_1]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1820,plain,
% 7.65/1.50      ( r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK5))
% 7.65/1.50      | k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,sK5)))) != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2234,plain,
% 7.65/1.50      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,sK5)))) = k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2504,plain,
% 7.65/1.50      ( ~ r1_tarski(k1_xboole_0,k5_relat_1(sK5,k1_xboole_0))
% 7.65/1.50      | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0)
% 7.65/1.50      | ~ r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_2501,c_1820,c_2234]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2505,plain,
% 7.65/1.50      ( ~ r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0)
% 7.65/1.50      | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0)
% 7.65/1.50      | ~ r1_tarski(k1_xboole_0,k5_relat_1(sK5,k1_xboole_0)) ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_2504]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7429,plain,
% 7.65/1.50      ( ~ r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0)
% 7.65/1.50      | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0) ),
% 7.65/1.50      inference(backward_subsumption_resolution,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_7216,c_2505]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7432,plain,
% 7.65/1.50      ( r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0) != iProver_top
% 7.65/1.50      | r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_7429]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_43,plain,
% 7.65/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f132]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_38,plain,
% 7.65/1.50      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 7.65/1.50      | ~ v1_relat_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f128]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1370,plain,
% 7.65/1.50      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 7.65/1.50      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5460,plain,
% 7.65/1.50      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 7.65/1.50      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_43,c_1370]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_42,plain,
% 7.65/1.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f133]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5474,plain,
% 7.65/1.50      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_5460,c_42]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15338,plain,
% 7.65/1.50      ( v1_relat_1(X0) != iProver_top
% 7.65/1.50      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 7.65/1.50      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_5474,c_2292]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15339,plain,
% 7.65/1.50      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_15338]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1388,plain,
% 7.65/1.50      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0
% 7.65/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10262,plain,
% 7.65/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_9,c_1388]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15345,plain,
% 7.65/1.50      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(forward_subsumption_resolution,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_15339,c_10262]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15352,plain,
% 7.65/1.50      ( k2_relat_1(k5_relat_1(sK5,k1_xboole_0)) = k1_xboole_0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1366,c_15345]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_33,plain,
% 7.65/1.50      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 7.65/1.50      | ~ v1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f123]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1375,plain,
% 7.65/1.50      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15430,plain,
% 7.65/1.50      ( r1_tarski(k5_relat_1(sK5,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK5,k1_xboole_0)),k1_xboole_0)) = iProver_top
% 7.65/1.50      | v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_15352,c_1375]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15451,plain,
% 7.65/1.50      ( r1_tarski(k5_relat_1(sK5,k1_xboole_0),k1_xboole_0) = iProver_top
% 7.65/1.50      | v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_15430,c_11]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_37,plain,
% 7.65/1.50      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 7.65/1.50      | ~ v1_relat_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f127]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1371,plain,
% 7.65/1.50      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 7.65/1.50      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6888,plain,
% 7.65/1.50      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 7.65/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_42,c_1371]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6920,plain,
% 7.65/1.50      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_6888,c_43]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17852,plain,
% 7.65/1.50      ( v1_relat_1(X0) != iProver_top
% 7.65/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.65/1.50      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_6920,c_2292]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17853,plain,
% 7.65/1.50      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_17852]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17859,plain,
% 7.65/1.50      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(forward_subsumption_resolution,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_17853,c_10262]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17866,plain,
% 7.65/1.50      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK5)) = k1_xboole_0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1366,c_17859]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18118,plain,
% 7.65/1.50      ( r1_tarski(k5_relat_1(k1_xboole_0,sK5),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK5)))) = iProver_top
% 7.65/1.50      | v1_relat_1(k5_relat_1(k1_xboole_0,sK5)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_17866,c_1375]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18139,plain,
% 7.65/1.50      ( r1_tarski(k5_relat_1(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
% 7.65/1.50      | v1_relat_1(k5_relat_1(k1_xboole_0,sK5)) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_18118,c_12]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_20450,plain,
% 7.65/1.50      ( v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_12257,c_46,c_2292,c_5838,c_7432,c_15451,c_18139]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_20455,plain,
% 7.65/1.50      ( v1_relat_1(sK5) != iProver_top
% 7.65/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1377,c_20450]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(contradiction,plain,
% 7.65/1.50      ( $false ),
% 7.65/1.50      inference(minisat,[status(thm)],[c_20455,c_2292,c_46]) ).
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  ------                               Statistics
% 7.65/1.50  
% 7.65/1.50  ------ Selected
% 7.65/1.50  
% 7.65/1.50  total_time:                             0.79
% 7.65/1.50  
%------------------------------------------------------------------------------
