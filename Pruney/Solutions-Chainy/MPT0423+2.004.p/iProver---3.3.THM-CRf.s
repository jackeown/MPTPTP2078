%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:22 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 630 expanded)
%              Number of clauses        :   75 ( 102 expanded)
%              Number of leaves         :   31 ( 178 expanded)
%              Depth                    :   15
%              Number of atoms          :  377 (1020 expanded)
%              Number of equality atoms :  223 ( 708 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f116])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f117])).

fof(f119,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f118])).

fof(f120,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f119])).

fof(f123,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f120])).

fof(f131,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f78,f123])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f136,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f105,f123])).

fof(f29,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_tarski(X0) = X1
       => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_tarski(X0) = X1
         => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f42,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f43,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f42])).

fof(f61,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
        & k1_tarski(X0) = X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4)
      & k1_tarski(sK3) = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4)
    & k1_tarski(sK3) = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f61])).

fof(f113,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f62])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f40])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f137,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
    inference(definition_unfolding,[],[f115,f123])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f48])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f77,f123,f123])).

fof(f139,plain,(
    ! [X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f128])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f73,f123])).

fof(f114,plain,(
    k1_tarski(sK3) = sK4 ),
    inference(cnf_transformation,[],[f62])).

fof(f138,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
    inference(definition_unfolding,[],[f114,f123])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f25,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f121,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f108,f120])).

fof(f122,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f64,f121])).

fof(f133,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f79,f122,f123,f123,f123])).

fof(f141,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f133])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f125,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f63,f121])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f37])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f75,f123,f123])).

fof(f17,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f21,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f124,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f104,f85])).

fof(f134,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f86,f124])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f135,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f102,f85])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f123])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_32,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1162,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2672,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1162])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1155,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1160,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3616,plain,
    ( k7_setfam_1(sK3,k7_setfam_1(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_1155,c_1160])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1156,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_7899,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3616,c_1156])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1475,plain,
    ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_1476,plain,
    ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1475])).

cnf(c_30754,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7899,c_42,c_1476])).

cnf(c_30769,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2672,c_30754])).

cnf(c_39,negated_conjecture,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_4,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_118,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_120,plain,
    ( r1_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1538,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1539,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1538])).

cnf(c_1541,plain,
    ( r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1539])).

cnf(c_396,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1999,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_40,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_9,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1356,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9,c_0,c_1])).

cnf(c_2664,plain,
    ( sK4 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_40,c_1356])).

cnf(c_3288,plain,
    ( k7_setfam_1(sK3,sK4) = k7_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1971,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k7_setfam_1(X0,sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3319,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | k7_setfam_1(sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1971])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_6088,plain,
    ( ~ r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k7_setfam_1(sK3,sK4)
    | k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6096,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k7_setfam_1(sK3,sK4)
    | k1_xboole_0 = k7_setfam_1(sK3,sK4)
    | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6088])).

cnf(c_6098,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k7_setfam_1(sK3,sK4)
    | k1_xboole_0 = k7_setfam_1(sK3,sK4)
    | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6096])).

cnf(c_397,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3284,plain,
    ( X0 != X1
    | k7_setfam_1(sK3,sK4) != X1
    | k7_setfam_1(sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_397])).

cnf(c_8890,plain,
    ( X0 != k7_setfam_1(sK3,sK4)
    | k7_setfam_1(sK3,sK4) = X0
    | k7_setfam_1(sK3,sK4) != k7_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3284])).

cnf(c_8891,plain,
    ( k7_setfam_1(sK3,sK4) != k7_setfam_1(sK3,sK4)
    | k7_setfam_1(sK3,sK4) = k1_xboole_0
    | k1_xboole_0 != k7_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_8890])).

cnf(c_3811,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_397])).

cnf(c_8992,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3811])).

cnf(c_8993,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_8992])).

cnf(c_14,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1158,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2012,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X1,k7_setfam_1(X1,X0)) = iProver_top
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1158])).

cnf(c_30,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1164,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5955,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X1,k7_setfam_1(X1,X0)) = iProver_top
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2012,c_1164])).

cnf(c_5961,plain,
    ( r2_hidden(X0,k7_setfam_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = iProver_top
    | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_5955])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1188,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5090,plain,
    ( r2_hidden(sK3,X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_40,c_1188])).

cnf(c_17589,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5961,c_5090])).

cnf(c_17606,plain,
    ( r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_17589])).

cnf(c_30765,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_30754])).

cnf(c_30819,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30765])).

cnf(c_31639,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30769,c_41,c_39,c_120,c_1541,c_1999,c_2664,c_3288,c_3319,c_6098,c_8891,c_8993,c_17606,c_30819])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1180,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3947,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_1180])).

cnf(c_31,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_64,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_67,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1460,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_8367,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3947,c_64,c_67,c_1460])).

cnf(c_31644,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_31639,c_8367])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:27:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.65/2.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.65/2.02  
% 11.65/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.65/2.02  
% 11.65/2.02  ------  iProver source info
% 11.65/2.02  
% 11.65/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.65/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.65/2.02  git: non_committed_changes: false
% 11.65/2.02  git: last_make_outside_of_git: false
% 11.65/2.02  
% 11.65/2.02  ------ 
% 11.65/2.02  
% 11.65/2.02  ------ Input Options
% 11.65/2.02  
% 11.65/2.02  --out_options                           all
% 11.65/2.02  --tptp_safe_out                         true
% 11.65/2.02  --problem_path                          ""
% 11.65/2.02  --include_path                          ""
% 11.65/2.02  --clausifier                            res/vclausify_rel
% 11.65/2.02  --clausifier_options                    --mode clausify
% 11.65/2.02  --stdin                                 false
% 11.65/2.02  --stats_out                             sel
% 11.65/2.02  
% 11.65/2.02  ------ General Options
% 11.65/2.02  
% 11.65/2.02  --fof                                   false
% 11.65/2.02  --time_out_real                         604.98
% 11.65/2.02  --time_out_virtual                      -1.
% 11.65/2.02  --symbol_type_check                     false
% 11.65/2.02  --clausify_out                          false
% 11.65/2.02  --sig_cnt_out                           false
% 11.65/2.02  --trig_cnt_out                          false
% 11.65/2.02  --trig_cnt_out_tolerance                1.
% 11.65/2.02  --trig_cnt_out_sk_spl                   false
% 11.65/2.02  --abstr_cl_out                          false
% 11.65/2.02  
% 11.65/2.02  ------ Global Options
% 11.65/2.02  
% 11.65/2.02  --schedule                              none
% 11.65/2.02  --add_important_lit                     false
% 11.65/2.02  --prop_solver_per_cl                    1000
% 11.65/2.02  --min_unsat_core                        false
% 11.65/2.02  --soft_assumptions                      false
% 11.65/2.02  --soft_lemma_size                       3
% 11.65/2.02  --prop_impl_unit_size                   0
% 11.65/2.02  --prop_impl_unit                        []
% 11.65/2.02  --share_sel_clauses                     true
% 11.65/2.02  --reset_solvers                         false
% 11.65/2.02  --bc_imp_inh                            [conj_cone]
% 11.65/2.02  --conj_cone_tolerance                   3.
% 11.65/2.02  --extra_neg_conj                        none
% 11.65/2.02  --large_theory_mode                     true
% 11.65/2.02  --prolific_symb_bound                   200
% 11.65/2.02  --lt_threshold                          2000
% 11.65/2.02  --clause_weak_htbl                      true
% 11.65/2.02  --gc_record_bc_elim                     false
% 11.65/2.02  
% 11.65/2.02  ------ Preprocessing Options
% 11.65/2.02  
% 11.65/2.02  --preprocessing_flag                    true
% 11.65/2.02  --time_out_prep_mult                    0.1
% 11.65/2.02  --splitting_mode                        input
% 11.65/2.02  --splitting_grd                         true
% 11.65/2.02  --splitting_cvd                         false
% 11.65/2.02  --splitting_cvd_svl                     false
% 11.65/2.02  --splitting_nvd                         32
% 11.65/2.02  --sub_typing                            true
% 11.65/2.02  --prep_gs_sim                           false
% 11.65/2.02  --prep_unflatten                        true
% 11.65/2.02  --prep_res_sim                          true
% 11.65/2.02  --prep_upred                            true
% 11.65/2.02  --prep_sem_filter                       exhaustive
% 11.65/2.02  --prep_sem_filter_out                   false
% 11.65/2.02  --pred_elim                             false
% 11.65/2.02  --res_sim_input                         true
% 11.65/2.02  --eq_ax_congr_red                       true
% 11.65/2.02  --pure_diseq_elim                       true
% 11.65/2.02  --brand_transform                       false
% 11.65/2.02  --non_eq_to_eq                          false
% 11.65/2.02  --prep_def_merge                        true
% 11.65/2.02  --prep_def_merge_prop_impl              false
% 11.65/2.02  --prep_def_merge_mbd                    true
% 11.65/2.02  --prep_def_merge_tr_red                 false
% 11.65/2.02  --prep_def_merge_tr_cl                  false
% 11.65/2.02  --smt_preprocessing                     true
% 11.65/2.02  --smt_ac_axioms                         fast
% 11.65/2.02  --preprocessed_out                      false
% 11.65/2.02  --preprocessed_stats                    false
% 11.65/2.02  
% 11.65/2.02  ------ Abstraction refinement Options
% 11.65/2.02  
% 11.65/2.02  --abstr_ref                             []
% 11.65/2.02  --abstr_ref_prep                        false
% 11.65/2.02  --abstr_ref_until_sat                   false
% 11.65/2.02  --abstr_ref_sig_restrict                funpre
% 11.65/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/2.02  --abstr_ref_under                       []
% 11.65/2.02  
% 11.65/2.02  ------ SAT Options
% 11.65/2.02  
% 11.65/2.02  --sat_mode                              false
% 11.65/2.02  --sat_fm_restart_options                ""
% 11.65/2.02  --sat_gr_def                            false
% 11.65/2.02  --sat_epr_types                         true
% 11.65/2.02  --sat_non_cyclic_types                  false
% 11.65/2.02  --sat_finite_models                     false
% 11.65/2.02  --sat_fm_lemmas                         false
% 11.65/2.02  --sat_fm_prep                           false
% 11.65/2.02  --sat_fm_uc_incr                        true
% 11.65/2.02  --sat_out_model                         small
% 11.65/2.02  --sat_out_clauses                       false
% 11.65/2.02  
% 11.65/2.02  ------ QBF Options
% 11.65/2.02  
% 11.65/2.02  --qbf_mode                              false
% 11.65/2.02  --qbf_elim_univ                         false
% 11.65/2.02  --qbf_dom_inst                          none
% 11.65/2.02  --qbf_dom_pre_inst                      false
% 11.65/2.02  --qbf_sk_in                             false
% 11.65/2.02  --qbf_pred_elim                         true
% 11.65/2.02  --qbf_split                             512
% 11.65/2.02  
% 11.65/2.02  ------ BMC1 Options
% 11.65/2.02  
% 11.65/2.02  --bmc1_incremental                      false
% 11.65/2.02  --bmc1_axioms                           reachable_all
% 11.65/2.02  --bmc1_min_bound                        0
% 11.65/2.02  --bmc1_max_bound                        -1
% 11.65/2.02  --bmc1_max_bound_default                -1
% 11.65/2.02  --bmc1_symbol_reachability              true
% 11.65/2.02  --bmc1_property_lemmas                  false
% 11.65/2.02  --bmc1_k_induction                      false
% 11.65/2.02  --bmc1_non_equiv_states                 false
% 11.65/2.02  --bmc1_deadlock                         false
% 11.65/2.02  --bmc1_ucm                              false
% 11.65/2.02  --bmc1_add_unsat_core                   none
% 11.65/2.02  --bmc1_unsat_core_children              false
% 11.65/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/2.02  --bmc1_out_stat                         full
% 11.65/2.02  --bmc1_ground_init                      false
% 11.65/2.02  --bmc1_pre_inst_next_state              false
% 11.65/2.02  --bmc1_pre_inst_state                   false
% 11.65/2.02  --bmc1_pre_inst_reach_state             false
% 11.65/2.02  --bmc1_out_unsat_core                   false
% 11.65/2.02  --bmc1_aig_witness_out                  false
% 11.65/2.02  --bmc1_verbose                          false
% 11.65/2.02  --bmc1_dump_clauses_tptp                false
% 11.65/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.65/2.02  --bmc1_dump_file                        -
% 11.65/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.65/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.65/2.02  --bmc1_ucm_extend_mode                  1
% 11.65/2.02  --bmc1_ucm_init_mode                    2
% 11.65/2.02  --bmc1_ucm_cone_mode                    none
% 11.65/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.65/2.02  --bmc1_ucm_relax_model                  4
% 11.65/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.65/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/2.02  --bmc1_ucm_layered_model                none
% 11.65/2.02  --bmc1_ucm_max_lemma_size               10
% 11.65/2.02  
% 11.65/2.02  ------ AIG Options
% 11.65/2.02  
% 11.65/2.02  --aig_mode                              false
% 11.65/2.02  
% 11.65/2.02  ------ Instantiation Options
% 11.65/2.02  
% 11.65/2.02  --instantiation_flag                    true
% 11.65/2.02  --inst_sos_flag                         false
% 11.65/2.02  --inst_sos_phase                        true
% 11.65/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/2.02  --inst_lit_sel_side                     num_symb
% 11.65/2.02  --inst_solver_per_active                1400
% 11.65/2.02  --inst_solver_calls_frac                1.
% 11.65/2.02  --inst_passive_queue_type               priority_queues
% 11.65/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/2.02  --inst_passive_queues_freq              [25;2]
% 11.65/2.02  --inst_dismatching                      true
% 11.65/2.02  --inst_eager_unprocessed_to_passive     true
% 11.65/2.02  --inst_prop_sim_given                   true
% 11.65/2.02  --inst_prop_sim_new                     false
% 11.65/2.02  --inst_subs_new                         false
% 11.65/2.02  --inst_eq_res_simp                      false
% 11.65/2.02  --inst_subs_given                       false
% 11.65/2.02  --inst_orphan_elimination               true
% 11.65/2.02  --inst_learning_loop_flag               true
% 11.65/2.02  --inst_learning_start                   3000
% 11.65/2.02  --inst_learning_factor                  2
% 11.65/2.02  --inst_start_prop_sim_after_learn       3
% 11.65/2.02  --inst_sel_renew                        solver
% 11.65/2.02  --inst_lit_activity_flag                true
% 11.65/2.02  --inst_restr_to_given                   false
% 11.65/2.02  --inst_activity_threshold               500
% 11.65/2.02  --inst_out_proof                        true
% 11.65/2.02  
% 11.65/2.02  ------ Resolution Options
% 11.65/2.02  
% 11.65/2.02  --resolution_flag                       true
% 11.65/2.02  --res_lit_sel                           adaptive
% 11.65/2.02  --res_lit_sel_side                      none
% 11.65/2.02  --res_ordering                          kbo
% 11.65/2.02  --res_to_prop_solver                    active
% 11.65/2.02  --res_prop_simpl_new                    false
% 11.65/2.02  --res_prop_simpl_given                  true
% 11.65/2.02  --res_passive_queue_type                priority_queues
% 11.65/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/2.02  --res_passive_queues_freq               [15;5]
% 11.65/2.02  --res_forward_subs                      full
% 11.65/2.02  --res_backward_subs                     full
% 11.65/2.02  --res_forward_subs_resolution           true
% 11.65/2.02  --res_backward_subs_resolution          true
% 11.65/2.02  --res_orphan_elimination                true
% 11.65/2.02  --res_time_limit                        2.
% 11.65/2.02  --res_out_proof                         true
% 11.65/2.02  
% 11.65/2.02  ------ Superposition Options
% 11.65/2.02  
% 11.65/2.02  --superposition_flag                    true
% 11.65/2.02  --sup_passive_queue_type                priority_queues
% 11.65/2.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/2.02  --sup_passive_queues_freq               [1;4]
% 11.65/2.02  --demod_completeness_check              fast
% 11.65/2.02  --demod_use_ground                      true
% 11.65/2.02  --sup_to_prop_solver                    passive
% 11.65/2.02  --sup_prop_simpl_new                    true
% 11.65/2.02  --sup_prop_simpl_given                  true
% 11.65/2.02  --sup_fun_splitting                     false
% 11.65/2.02  --sup_smt_interval                      50000
% 11.65/2.02  
% 11.65/2.02  ------ Superposition Simplification Setup
% 11.65/2.02  
% 11.65/2.02  --sup_indices_passive                   []
% 11.65/2.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.02  --sup_full_bw                           [BwDemod]
% 11.65/2.02  --sup_immed_triv                        [TrivRules]
% 11.65/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.02  --sup_immed_bw_main                     []
% 11.65/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.65/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.65/2.02  
% 11.65/2.02  ------ Combination Options
% 11.65/2.02  
% 11.65/2.02  --comb_res_mult                         3
% 11.65/2.02  --comb_sup_mult                         2
% 11.65/2.02  --comb_inst_mult                        10
% 11.65/2.02  
% 11.65/2.02  ------ Debug Options
% 11.65/2.02  
% 11.65/2.02  --dbg_backtrace                         false
% 11.65/2.02  --dbg_dump_prop_clauses                 false
% 11.65/2.02  --dbg_dump_prop_clauses_file            -
% 11.65/2.02  --dbg_out_stat                          false
% 11.65/2.02  ------ Parsing...
% 11.65/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.65/2.02  
% 11.65/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.65/2.02  
% 11.65/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.65/2.02  
% 11.65/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.65/2.02  ------ Proving...
% 11.65/2.02  ------ Problem Properties 
% 11.65/2.02  
% 11.65/2.02  
% 11.65/2.02  clauses                                 42
% 11.65/2.02  conjectures                             3
% 11.65/2.02  EPR                                     15
% 11.65/2.02  Horn                                    36
% 11.65/2.02  unary                                   21
% 11.65/2.02  binary                                  7
% 11.65/2.02  lits                                    86
% 11.65/2.02  lits eq                                 23
% 11.65/2.02  fd_pure                                 0
% 11.65/2.02  fd_pseudo                               0
% 11.65/2.02  fd_cond                                 1
% 11.65/2.02  fd_pseudo_cond                          4
% 11.65/2.02  AC symbols                              0
% 11.65/2.02  
% 11.65/2.02  ------ Input Options Time Limit: Unbounded
% 11.65/2.02  
% 11.65/2.02  
% 11.65/2.02  ------ 
% 11.65/2.02  Current options:
% 11.65/2.02  ------ 
% 11.65/2.02  
% 11.65/2.02  ------ Input Options
% 11.65/2.02  
% 11.65/2.02  --out_options                           all
% 11.65/2.02  --tptp_safe_out                         true
% 11.65/2.02  --problem_path                          ""
% 11.65/2.02  --include_path                          ""
% 11.65/2.02  --clausifier                            res/vclausify_rel
% 11.65/2.02  --clausifier_options                    --mode clausify
% 11.65/2.02  --stdin                                 false
% 11.65/2.02  --stats_out                             sel
% 11.65/2.02  
% 11.65/2.02  ------ General Options
% 11.65/2.02  
% 11.65/2.02  --fof                                   false
% 11.65/2.02  --time_out_real                         604.98
% 11.65/2.02  --time_out_virtual                      -1.
% 11.65/2.02  --symbol_type_check                     false
% 11.65/2.02  --clausify_out                          false
% 11.65/2.02  --sig_cnt_out                           false
% 11.65/2.02  --trig_cnt_out                          false
% 11.65/2.02  --trig_cnt_out_tolerance                1.
% 11.65/2.02  --trig_cnt_out_sk_spl                   false
% 11.65/2.02  --abstr_cl_out                          false
% 11.65/2.02  
% 11.65/2.02  ------ Global Options
% 11.65/2.02  
% 11.65/2.02  --schedule                              none
% 11.65/2.02  --add_important_lit                     false
% 11.65/2.02  --prop_solver_per_cl                    1000
% 11.65/2.02  --min_unsat_core                        false
% 11.65/2.02  --soft_assumptions                      false
% 11.65/2.02  --soft_lemma_size                       3
% 11.65/2.02  --prop_impl_unit_size                   0
% 11.65/2.02  --prop_impl_unit                        []
% 11.65/2.02  --share_sel_clauses                     true
% 11.65/2.02  --reset_solvers                         false
% 11.65/2.02  --bc_imp_inh                            [conj_cone]
% 11.65/2.02  --conj_cone_tolerance                   3.
% 11.65/2.02  --extra_neg_conj                        none
% 11.65/2.02  --large_theory_mode                     true
% 11.65/2.02  --prolific_symb_bound                   200
% 11.65/2.02  --lt_threshold                          2000
% 11.65/2.02  --clause_weak_htbl                      true
% 11.65/2.02  --gc_record_bc_elim                     false
% 11.65/2.02  
% 11.65/2.02  ------ Preprocessing Options
% 11.65/2.02  
% 11.65/2.02  --preprocessing_flag                    true
% 11.65/2.02  --time_out_prep_mult                    0.1
% 11.65/2.02  --splitting_mode                        input
% 11.65/2.02  --splitting_grd                         true
% 11.65/2.02  --splitting_cvd                         false
% 11.65/2.02  --splitting_cvd_svl                     false
% 11.65/2.02  --splitting_nvd                         32
% 11.65/2.02  --sub_typing                            true
% 11.65/2.02  --prep_gs_sim                           false
% 11.65/2.02  --prep_unflatten                        true
% 11.65/2.02  --prep_res_sim                          true
% 11.65/2.02  --prep_upred                            true
% 11.65/2.02  --prep_sem_filter                       exhaustive
% 11.65/2.02  --prep_sem_filter_out                   false
% 11.65/2.02  --pred_elim                             false
% 11.65/2.02  --res_sim_input                         true
% 11.65/2.02  --eq_ax_congr_red                       true
% 11.65/2.02  --pure_diseq_elim                       true
% 11.65/2.02  --brand_transform                       false
% 11.65/2.02  --non_eq_to_eq                          false
% 11.65/2.02  --prep_def_merge                        true
% 11.65/2.02  --prep_def_merge_prop_impl              false
% 11.65/2.02  --prep_def_merge_mbd                    true
% 11.65/2.02  --prep_def_merge_tr_red                 false
% 11.65/2.02  --prep_def_merge_tr_cl                  false
% 11.65/2.02  --smt_preprocessing                     true
% 11.65/2.02  --smt_ac_axioms                         fast
% 11.65/2.02  --preprocessed_out                      false
% 11.65/2.02  --preprocessed_stats                    false
% 11.65/2.02  
% 11.65/2.02  ------ Abstraction refinement Options
% 11.65/2.02  
% 11.65/2.02  --abstr_ref                             []
% 11.65/2.02  --abstr_ref_prep                        false
% 11.65/2.02  --abstr_ref_until_sat                   false
% 11.65/2.02  --abstr_ref_sig_restrict                funpre
% 11.65/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/2.02  --abstr_ref_under                       []
% 11.65/2.02  
% 11.65/2.02  ------ SAT Options
% 11.65/2.02  
% 11.65/2.02  --sat_mode                              false
% 11.65/2.02  --sat_fm_restart_options                ""
% 11.65/2.02  --sat_gr_def                            false
% 11.65/2.02  --sat_epr_types                         true
% 11.65/2.02  --sat_non_cyclic_types                  false
% 11.65/2.02  --sat_finite_models                     false
% 11.65/2.02  --sat_fm_lemmas                         false
% 11.65/2.02  --sat_fm_prep                           false
% 11.65/2.02  --sat_fm_uc_incr                        true
% 11.65/2.02  --sat_out_model                         small
% 11.65/2.02  --sat_out_clauses                       false
% 11.65/2.02  
% 11.65/2.02  ------ QBF Options
% 11.65/2.02  
% 11.65/2.02  --qbf_mode                              false
% 11.65/2.02  --qbf_elim_univ                         false
% 11.65/2.02  --qbf_dom_inst                          none
% 11.65/2.02  --qbf_dom_pre_inst                      false
% 11.65/2.02  --qbf_sk_in                             false
% 11.65/2.02  --qbf_pred_elim                         true
% 11.65/2.02  --qbf_split                             512
% 11.65/2.02  
% 11.65/2.02  ------ BMC1 Options
% 11.65/2.02  
% 11.65/2.02  --bmc1_incremental                      false
% 11.65/2.02  --bmc1_axioms                           reachable_all
% 11.65/2.02  --bmc1_min_bound                        0
% 11.65/2.02  --bmc1_max_bound                        -1
% 11.65/2.02  --bmc1_max_bound_default                -1
% 11.65/2.02  --bmc1_symbol_reachability              true
% 11.65/2.02  --bmc1_property_lemmas                  false
% 11.65/2.02  --bmc1_k_induction                      false
% 11.65/2.02  --bmc1_non_equiv_states                 false
% 11.65/2.02  --bmc1_deadlock                         false
% 11.65/2.02  --bmc1_ucm                              false
% 11.65/2.02  --bmc1_add_unsat_core                   none
% 11.65/2.02  --bmc1_unsat_core_children              false
% 11.65/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/2.02  --bmc1_out_stat                         full
% 11.65/2.02  --bmc1_ground_init                      false
% 11.65/2.02  --bmc1_pre_inst_next_state              false
% 11.65/2.02  --bmc1_pre_inst_state                   false
% 11.65/2.02  --bmc1_pre_inst_reach_state             false
% 11.65/2.02  --bmc1_out_unsat_core                   false
% 11.65/2.02  --bmc1_aig_witness_out                  false
% 11.65/2.02  --bmc1_verbose                          false
% 11.65/2.02  --bmc1_dump_clauses_tptp                false
% 11.65/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.65/2.02  --bmc1_dump_file                        -
% 11.65/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.65/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.65/2.02  --bmc1_ucm_extend_mode                  1
% 11.65/2.02  --bmc1_ucm_init_mode                    2
% 11.65/2.02  --bmc1_ucm_cone_mode                    none
% 11.65/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.65/2.02  --bmc1_ucm_relax_model                  4
% 11.65/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.65/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/2.02  --bmc1_ucm_layered_model                none
% 11.65/2.02  --bmc1_ucm_max_lemma_size               10
% 11.65/2.02  
% 11.65/2.02  ------ AIG Options
% 11.65/2.02  
% 11.65/2.02  --aig_mode                              false
% 11.65/2.02  
% 11.65/2.02  ------ Instantiation Options
% 11.65/2.02  
% 11.65/2.02  --instantiation_flag                    true
% 11.65/2.02  --inst_sos_flag                         false
% 11.65/2.02  --inst_sos_phase                        true
% 11.65/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/2.02  --inst_lit_sel_side                     num_symb
% 11.65/2.02  --inst_solver_per_active                1400
% 11.65/2.02  --inst_solver_calls_frac                1.
% 11.65/2.02  --inst_passive_queue_type               priority_queues
% 11.65/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/2.02  --inst_passive_queues_freq              [25;2]
% 11.65/2.02  --inst_dismatching                      true
% 11.65/2.02  --inst_eager_unprocessed_to_passive     true
% 11.65/2.02  --inst_prop_sim_given                   true
% 11.65/2.02  --inst_prop_sim_new                     false
% 11.65/2.02  --inst_subs_new                         false
% 11.65/2.02  --inst_eq_res_simp                      false
% 11.65/2.02  --inst_subs_given                       false
% 11.65/2.02  --inst_orphan_elimination               true
% 11.65/2.02  --inst_learning_loop_flag               true
% 11.65/2.02  --inst_learning_start                   3000
% 11.65/2.02  --inst_learning_factor                  2
% 11.65/2.02  --inst_start_prop_sim_after_learn       3
% 11.65/2.02  --inst_sel_renew                        solver
% 11.65/2.02  --inst_lit_activity_flag                true
% 11.65/2.02  --inst_restr_to_given                   false
% 11.65/2.02  --inst_activity_threshold               500
% 11.65/2.02  --inst_out_proof                        true
% 11.65/2.02  
% 11.65/2.02  ------ Resolution Options
% 11.65/2.02  
% 11.65/2.02  --resolution_flag                       true
% 11.65/2.02  --res_lit_sel                           adaptive
% 11.65/2.02  --res_lit_sel_side                      none
% 11.65/2.02  --res_ordering                          kbo
% 11.65/2.02  --res_to_prop_solver                    active
% 11.65/2.02  --res_prop_simpl_new                    false
% 11.65/2.02  --res_prop_simpl_given                  true
% 11.65/2.02  --res_passive_queue_type                priority_queues
% 11.65/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/2.02  --res_passive_queues_freq               [15;5]
% 11.65/2.02  --res_forward_subs                      full
% 11.65/2.02  --res_backward_subs                     full
% 11.65/2.02  --res_forward_subs_resolution           true
% 11.65/2.02  --res_backward_subs_resolution          true
% 11.65/2.02  --res_orphan_elimination                true
% 11.65/2.02  --res_time_limit                        2.
% 11.65/2.02  --res_out_proof                         true
% 11.65/2.02  
% 11.65/2.02  ------ Superposition Options
% 11.65/2.02  
% 11.65/2.02  --superposition_flag                    true
% 11.65/2.02  --sup_passive_queue_type                priority_queues
% 11.65/2.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/2.02  --sup_passive_queues_freq               [1;4]
% 11.65/2.02  --demod_completeness_check              fast
% 11.65/2.02  --demod_use_ground                      true
% 11.65/2.02  --sup_to_prop_solver                    passive
% 11.65/2.02  --sup_prop_simpl_new                    true
% 11.65/2.02  --sup_prop_simpl_given                  true
% 11.65/2.02  --sup_fun_splitting                     false
% 11.65/2.02  --sup_smt_interval                      50000
% 11.65/2.02  
% 11.65/2.02  ------ Superposition Simplification Setup
% 11.65/2.02  
% 11.65/2.02  --sup_indices_passive                   []
% 11.65/2.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.02  --sup_full_bw                           [BwDemod]
% 11.65/2.02  --sup_immed_triv                        [TrivRules]
% 11.65/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.02  --sup_immed_bw_main                     []
% 11.65/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.65/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.65/2.02  
% 11.65/2.02  ------ Combination Options
% 11.65/2.02  
% 11.65/2.02  --comb_res_mult                         3
% 11.65/2.02  --comb_sup_mult                         2
% 11.65/2.02  --comb_inst_mult                        10
% 11.65/2.02  
% 11.65/2.02  ------ Debug Options
% 11.65/2.02  
% 11.65/2.02  --dbg_backtrace                         false
% 11.65/2.02  --dbg_dump_prop_clauses                 false
% 11.65/2.02  --dbg_dump_prop_clauses_file            -
% 11.65/2.02  --dbg_out_stat                          false
% 11.65/2.02  
% 11.65/2.02  
% 11.65/2.02  
% 11.65/2.02  
% 11.65/2.02  ------ Proving...
% 11.65/2.02  
% 11.65/2.02  
% 11.65/2.02  % SZS status Theorem for theBenchmark.p
% 11.65/2.02  
% 11.65/2.02   Resolution empty clause
% 11.65/2.02  
% 11.65/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.65/2.02  
% 11.65/2.02  fof(f13,axiom,(
% 11.65/2.02    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f78,plain,(
% 11.65/2.02    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 11.65/2.02    inference(cnf_transformation,[],[f13])).
% 11.65/2.02  
% 11.65/2.02  fof(f4,axiom,(
% 11.65/2.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f66,plain,(
% 11.65/2.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f4])).
% 11.65/2.02  
% 11.65/2.02  fof(f5,axiom,(
% 11.65/2.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f67,plain,(
% 11.65/2.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f5])).
% 11.65/2.02  
% 11.65/2.02  fof(f6,axiom,(
% 11.65/2.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f68,plain,(
% 11.65/2.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f6])).
% 11.65/2.02  
% 11.65/2.02  fof(f7,axiom,(
% 11.65/2.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f69,plain,(
% 11.65/2.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f7])).
% 11.65/2.02  
% 11.65/2.02  fof(f8,axiom,(
% 11.65/2.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f70,plain,(
% 11.65/2.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f8])).
% 11.65/2.02  
% 11.65/2.02  fof(f9,axiom,(
% 11.65/2.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f71,plain,(
% 11.65/2.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f9])).
% 11.65/2.02  
% 11.65/2.02  fof(f10,axiom,(
% 11.65/2.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f72,plain,(
% 11.65/2.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f10])).
% 11.65/2.02  
% 11.65/2.02  fof(f116,plain,(
% 11.65/2.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f71,f72])).
% 11.65/2.02  
% 11.65/2.02  fof(f117,plain,(
% 11.65/2.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f70,f116])).
% 11.65/2.02  
% 11.65/2.02  fof(f118,plain,(
% 11.65/2.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f69,f117])).
% 11.65/2.02  
% 11.65/2.02  fof(f119,plain,(
% 11.65/2.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f68,f118])).
% 11.65/2.02  
% 11.65/2.02  fof(f120,plain,(
% 11.65/2.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f67,f119])).
% 11.65/2.02  
% 11.65/2.02  fof(f123,plain,(
% 11.65/2.02    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f66,f120])).
% 11.65/2.02  
% 11.65/2.02  fof(f131,plain,(
% 11.65/2.02    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 11.65/2.02    inference(definition_unfolding,[],[f78,f123])).
% 11.65/2.02  
% 11.65/2.02  fof(f22,axiom,(
% 11.65/2.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f34,plain,(
% 11.65/2.02    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 11.65/2.02    inference(ennf_transformation,[],[f22])).
% 11.65/2.02  
% 11.65/2.02  fof(f105,plain,(
% 11.65/2.02    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f34])).
% 11.65/2.02  
% 11.65/2.02  fof(f136,plain,(
% 11.65/2.02    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f105,f123])).
% 11.65/2.02  
% 11.65/2.02  fof(f29,conjecture,(
% 11.65/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f30,negated_conjecture,(
% 11.65/2.02    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 11.65/2.02    inference(negated_conjecture,[],[f29])).
% 11.65/2.02  
% 11.65/2.02  fof(f42,plain,(
% 11.65/2.02    ? [X0,X1] : ((k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    inference(ennf_transformation,[],[f30])).
% 11.65/2.02  
% 11.65/2.02  fof(f43,plain,(
% 11.65/2.02    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    inference(flattening,[],[f42])).
% 11.65/2.02  
% 11.65/2.02  fof(f61,plain,(
% 11.65/2.02    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4) & k1_tarski(sK3) = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 11.65/2.02    introduced(choice_axiom,[])).
% 11.65/2.02  
% 11.65/2.02  fof(f62,plain,(
% 11.65/2.02    k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4) & k1_tarski(sK3) = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 11.65/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f61])).
% 11.65/2.02  
% 11.65/2.02  fof(f113,plain,(
% 11.65/2.02    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 11.65/2.02    inference(cnf_transformation,[],[f62])).
% 11.65/2.02  
% 11.65/2.02  fof(f24,axiom,(
% 11.65/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f36,plain,(
% 11.65/2.02    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    inference(ennf_transformation,[],[f24])).
% 11.65/2.02  
% 11.65/2.02  fof(f107,plain,(
% 11.65/2.02    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f36])).
% 11.65/2.02  
% 11.65/2.02  fof(f28,axiom,(
% 11.65/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f40,plain,(
% 11.65/2.02    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    inference(ennf_transformation,[],[f28])).
% 11.65/2.02  
% 11.65/2.02  fof(f41,plain,(
% 11.65/2.02    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    inference(flattening,[],[f40])).
% 11.65/2.02  
% 11.65/2.02  fof(f112,plain,(
% 11.65/2.02    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f41])).
% 11.65/2.02  
% 11.65/2.02  fof(f23,axiom,(
% 11.65/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f35,plain,(
% 11.65/2.02    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    inference(ennf_transformation,[],[f23])).
% 11.65/2.02  
% 11.65/2.02  fof(f106,plain,(
% 11.65/2.02    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f35])).
% 11.65/2.02  
% 11.65/2.02  fof(f115,plain,(
% 11.65/2.02    k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4)),
% 11.65/2.02    inference(cnf_transformation,[],[f62])).
% 11.65/2.02  
% 11.65/2.02  fof(f137,plain,(
% 11.65/2.02    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4)),
% 11.65/2.02    inference(definition_unfolding,[],[f115,f123])).
% 11.65/2.02  
% 11.65/2.02  fof(f12,axiom,(
% 11.65/2.02    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f48,plain,(
% 11.65/2.02    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 11.65/2.02    inference(nnf_transformation,[],[f12])).
% 11.65/2.02  
% 11.65/2.02  fof(f49,plain,(
% 11.65/2.02    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 11.65/2.02    inference(flattening,[],[f48])).
% 11.65/2.02  
% 11.65/2.02  fof(f77,plain,(
% 11.65/2.02    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 11.65/2.02    inference(cnf_transformation,[],[f49])).
% 11.65/2.02  
% 11.65/2.02  fof(f128,plain,(
% 11.65/2.02    ( ! [X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 11.65/2.02    inference(definition_unfolding,[],[f77,f123,f123])).
% 11.65/2.02  
% 11.65/2.02  fof(f139,plain,(
% 11.65/2.02    ( ! [X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 11.65/2.02    inference(equality_resolution,[],[f128])).
% 11.65/2.02  
% 11.65/2.02  fof(f11,axiom,(
% 11.65/2.02    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f47,plain,(
% 11.65/2.02    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.65/2.02    inference(nnf_transformation,[],[f11])).
% 11.65/2.02  
% 11.65/2.02  fof(f73,plain,(
% 11.65/2.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f47])).
% 11.65/2.02  
% 11.65/2.02  fof(f127,plain,(
% 11.65/2.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f73,f123])).
% 11.65/2.02  
% 11.65/2.02  fof(f114,plain,(
% 11.65/2.02    k1_tarski(sK3) = sK4),
% 11.65/2.02    inference(cnf_transformation,[],[f62])).
% 11.65/2.02  
% 11.65/2.02  fof(f138,plain,(
% 11.65/2.02    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4),
% 11.65/2.02    inference(definition_unfolding,[],[f114,f123])).
% 11.65/2.02  
% 11.65/2.02  fof(f14,axiom,(
% 11.65/2.02    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f50,plain,(
% 11.65/2.02    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.65/2.02    inference(nnf_transformation,[],[f14])).
% 11.65/2.02  
% 11.65/2.02  fof(f79,plain,(
% 11.65/2.02    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f50])).
% 11.65/2.02  
% 11.65/2.02  fof(f2,axiom,(
% 11.65/2.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f64,plain,(
% 11.65/2.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f2])).
% 11.65/2.02  
% 11.65/2.02  fof(f25,axiom,(
% 11.65/2.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f108,plain,(
% 11.65/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f25])).
% 11.65/2.02  
% 11.65/2.02  fof(f121,plain,(
% 11.65/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.65/2.02    inference(definition_unfolding,[],[f108,f120])).
% 11.65/2.02  
% 11.65/2.02  fof(f122,plain,(
% 11.65/2.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.65/2.02    inference(definition_unfolding,[],[f64,f121])).
% 11.65/2.02  
% 11.65/2.02  fof(f133,plain,(
% 11.65/2.02    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f79,f122,f123,f123,f123])).
% 11.65/2.02  
% 11.65/2.02  fof(f141,plain,(
% 11.65/2.02    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 11.65/2.02    inference(equality_resolution,[],[f133])).
% 11.65/2.02  
% 11.65/2.02  fof(f1,axiom,(
% 11.65/2.02    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f31,plain,(
% 11.65/2.02    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.65/2.02    inference(rectify,[],[f1])).
% 11.65/2.02  
% 11.65/2.02  fof(f63,plain,(
% 11.65/2.02    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.65/2.02    inference(cnf_transformation,[],[f31])).
% 11.65/2.02  
% 11.65/2.02  fof(f125,plain,(
% 11.65/2.02    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 11.65/2.02    inference(definition_unfolding,[],[f63,f121])).
% 11.65/2.02  
% 11.65/2.02  fof(f3,axiom,(
% 11.65/2.02    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f65,plain,(
% 11.65/2.02    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.65/2.02    inference(cnf_transformation,[],[f3])).
% 11.65/2.02  
% 11.65/2.02  fof(f26,axiom,(
% 11.65/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f37,plain,(
% 11.65/2.02    ! [X0,X1] : ((k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    inference(ennf_transformation,[],[f26])).
% 11.65/2.02  
% 11.65/2.02  fof(f38,plain,(
% 11.65/2.02    ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    inference(flattening,[],[f37])).
% 11.65/2.02  
% 11.65/2.02  fof(f109,plain,(
% 11.65/2.02    ( ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f38])).
% 11.65/2.02  
% 11.65/2.02  fof(f75,plain,(
% 11.65/2.02    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f49])).
% 11.65/2.02  
% 11.65/2.02  fof(f130,plain,(
% 11.65/2.02    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 11.65/2.02    inference(definition_unfolding,[],[f75,f123,f123])).
% 11.65/2.02  
% 11.65/2.02  fof(f17,axiom,(
% 11.65/2.02    ! [X0] : k2_subset_1(X0) = X0),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f86,plain,(
% 11.65/2.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.65/2.02    inference(cnf_transformation,[],[f17])).
% 11.65/2.02  
% 11.65/2.02  fof(f21,axiom,(
% 11.65/2.02    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f104,plain,(
% 11.65/2.02    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f21])).
% 11.65/2.02  
% 11.65/2.02  fof(f16,axiom,(
% 11.65/2.02    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f85,plain,(
% 11.65/2.02    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f16])).
% 11.65/2.02  
% 11.65/2.02  fof(f124,plain,(
% 11.65/2.02    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f104,f85])).
% 11.65/2.02  
% 11.65/2.02  fof(f134,plain,(
% 11.65/2.02    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 11.65/2.02    inference(definition_unfolding,[],[f86,f124])).
% 11.65/2.02  
% 11.65/2.02  fof(f27,axiom,(
% 11.65/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f39,plain,(
% 11.65/2.02    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    inference(ennf_transformation,[],[f27])).
% 11.65/2.02  
% 11.65/2.02  fof(f60,plain,(
% 11.65/2.02    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.65/2.02    inference(nnf_transformation,[],[f39])).
% 11.65/2.02  
% 11.65/2.02  fof(f111,plain,(
% 11.65/2.02    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f60])).
% 11.65/2.02  
% 11.65/2.02  fof(f19,axiom,(
% 11.65/2.02    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f102,plain,(
% 11.65/2.02    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f19])).
% 11.65/2.02  
% 11.65/2.02  fof(f135,plain,(
% 11.65/2.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.65/2.02    inference(definition_unfolding,[],[f102,f85])).
% 11.65/2.02  
% 11.65/2.02  fof(f74,plain,(
% 11.65/2.02    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f47])).
% 11.65/2.02  
% 11.65/2.02  fof(f126,plain,(
% 11.65/2.02    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.65/2.02    inference(definition_unfolding,[],[f74,f123])).
% 11.65/2.02  
% 11.65/2.02  fof(f15,axiom,(
% 11.65/2.02    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f32,plain,(
% 11.65/2.02    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.65/2.02    inference(ennf_transformation,[],[f15])).
% 11.65/2.02  
% 11.65/2.02  fof(f51,plain,(
% 11.65/2.02    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.65/2.02    inference(nnf_transformation,[],[f32])).
% 11.65/2.02  
% 11.65/2.02  fof(f81,plain,(
% 11.65/2.02    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.65/2.02    inference(cnf_transformation,[],[f51])).
% 11.65/2.02  
% 11.65/2.02  fof(f20,axiom,(
% 11.65/2.02    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.65/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.02  
% 11.65/2.02  fof(f103,plain,(
% 11.65/2.02    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.65/2.02    inference(cnf_transformation,[],[f20])).
% 11.65/2.02  
% 11.65/2.02  cnf(c_7,plain,
% 11.65/2.02      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 11.65/2.02      inference(cnf_transformation,[],[f131]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_32,plain,
% 11.65/2.02      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
% 11.65/2.02      | ~ r2_hidden(X0,X1) ),
% 11.65/2.02      inference(cnf_transformation,[],[f136]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1162,plain,
% 11.65/2.02      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 11.65/2.02      | r2_hidden(X0,X1) != iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_2672,plain,
% 11.65/2.02      ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 11.65/2.02      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_7,c_1162]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_41,negated_conjecture,
% 11.65/2.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 11.65/2.02      inference(cnf_transformation,[],[f113]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1155,plain,
% 11.65/2.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_34,plain,
% 11.65/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.65/2.02      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 11.65/2.02      inference(cnf_transformation,[],[f107]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1160,plain,
% 11.65/2.02      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 11.65/2.02      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_3616,plain,
% 11.65/2.02      ( k7_setfam_1(sK3,k7_setfam_1(sK3,sK4)) = sK4 ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_1155,c_1160]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_38,plain,
% 11.65/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.65/2.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.65/2.02      | r1_tarski(X0,X2)
% 11.65/2.02      | ~ r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 11.65/2.02      inference(cnf_transformation,[],[f112]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1156,plain,
% 11.65/2.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.65/2.02      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.65/2.02      | r1_tarski(X0,X2) = iProver_top
% 11.65/2.02      | r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_7899,plain,
% 11.65/2.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 11.65/2.02      | m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 11.65/2.02      | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
% 11.65/2.02      | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_3616,c_1156]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_42,plain,
% 11.65/2.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_33,plain,
% 11.65/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.65/2.02      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 11.65/2.02      inference(cnf_transformation,[],[f106]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1475,plain,
% 11.65/2.02      ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3)))
% 11.65/2.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_33]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1476,plain,
% 11.65/2.02      ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top
% 11.65/2.02      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_1475]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_30754,plain,
% 11.65/2.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 11.65/2.02      | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
% 11.65/2.02      | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
% 11.65/2.02      inference(global_propositional_subsumption,
% 11.65/2.02                [status(thm)],
% 11.65/2.02                [c_7899,c_42,c_1476]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_30769,plain,
% 11.65/2.02      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 11.65/2.02      | r1_tarski(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.65/2.02      | r1_tarski(sK4,k7_setfam_1(sK3,k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_2672,c_30754]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_39,negated_conjecture,
% 11.65/2.02      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
% 11.65/2.02      inference(cnf_transformation,[],[f137]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_4,plain,
% 11.65/2.02      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 11.65/2.02      inference(cnf_transformation,[],[f139]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_118,plain,
% 11.65/2.02      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_120,plain,
% 11.65/2.02      ( r1_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_118]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_3,plain,
% 11.65/2.02      ( r2_hidden(X0,X1)
% 11.65/2.02      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 11.65/2.02      inference(cnf_transformation,[],[f127]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1538,plain,
% 11.65/2.02      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 11.65/2.02      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_3]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1539,plain,
% 11.65/2.02      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top
% 11.65/2.02      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_1538]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1541,plain,
% 11.65/2.02      ( r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
% 11.65/2.02      | r1_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_1539]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_396,plain,( X0 = X0 ),theory(equality) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1999,plain,
% 11.65/2.02      ( sK4 = sK4 ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_396]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_40,negated_conjecture,
% 11.65/2.02      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
% 11.65/2.02      inference(cnf_transformation,[],[f138]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_9,plain,
% 11.65/2.02      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.65/2.02      inference(cnf_transformation,[],[f141]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_0,plain,
% 11.65/2.02      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 11.65/2.02      inference(cnf_transformation,[],[f125]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1,plain,
% 11.65/2.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.65/2.02      inference(cnf_transformation,[],[f65]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1356,plain,
% 11.65/2.02      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 11.65/2.02      inference(demodulation,[status(thm)],[c_9,c_0,c_1]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_2664,plain,
% 11.65/2.02      ( sK4 != k1_xboole_0 ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_40,c_1356]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_3288,plain,
% 11.65/2.02      ( k7_setfam_1(sK3,sK4) = k7_setfam_1(sK3,sK4) ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_396]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_35,plain,
% 11.65/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.65/2.02      | k7_setfam_1(X1,X0) != k1_xboole_0
% 11.65/2.02      | k1_xboole_0 = X0 ),
% 11.65/2.02      inference(cnf_transformation,[],[f109]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1971,plain,
% 11.65/2.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 11.65/2.02      | k7_setfam_1(X0,sK4) != k1_xboole_0
% 11.65/2.02      | k1_xboole_0 = sK4 ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_35]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_3319,plain,
% 11.65/2.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))
% 11.65/2.02      | k7_setfam_1(sK3,sK4) != k1_xboole_0
% 11.65/2.02      | k1_xboole_0 = sK4 ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_1971]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_6,plain,
% 11.65/2.02      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 11.65/2.02      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 11.65/2.02      | k1_xboole_0 = X0 ),
% 11.65/2.02      inference(cnf_transformation,[],[f130]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_6088,plain,
% 11.65/2.02      ( ~ r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 11.65/2.02      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k7_setfam_1(sK3,sK4)
% 11.65/2.02      | k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_6]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_6096,plain,
% 11.65/2.02      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k7_setfam_1(sK3,sK4)
% 11.65/2.02      | k1_xboole_0 = k7_setfam_1(sK3,sK4)
% 11.65/2.02      | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_6088]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_6098,plain,
% 11.65/2.02      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k7_setfam_1(sK3,sK4)
% 11.65/2.02      | k1_xboole_0 = k7_setfam_1(sK3,sK4)
% 11.65/2.02      | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_6096]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_397,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_3284,plain,
% 11.65/2.02      ( X0 != X1 | k7_setfam_1(sK3,sK4) != X1 | k7_setfam_1(sK3,sK4) = X0 ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_397]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_8890,plain,
% 11.65/2.02      ( X0 != k7_setfam_1(sK3,sK4)
% 11.65/2.02      | k7_setfam_1(sK3,sK4) = X0
% 11.65/2.02      | k7_setfam_1(sK3,sK4) != k7_setfam_1(sK3,sK4) ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_3284]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_8891,plain,
% 11.65/2.02      ( k7_setfam_1(sK3,sK4) != k7_setfam_1(sK3,sK4)
% 11.65/2.02      | k7_setfam_1(sK3,sK4) = k1_xboole_0
% 11.65/2.02      | k1_xboole_0 != k7_setfam_1(sK3,sK4) ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_8890]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_3811,plain,
% 11.65/2.02      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_397]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_8992,plain,
% 11.65/2.02      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_3811]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_8993,plain,
% 11.65/2.02      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_8992]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_14,plain,
% 11.65/2.02      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 11.65/2.02      inference(cnf_transformation,[],[f134]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_36,plain,
% 11.65/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.65/2.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.65/2.02      | ~ r2_hidden(X0,X2)
% 11.65/2.02      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 11.65/2.02      inference(cnf_transformation,[],[f111]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1158,plain,
% 11.65/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.65/2.02      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.65/2.02      | r2_hidden(X0,X2) != iProver_top
% 11.65/2.02      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) = iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_2012,plain,
% 11.65/2.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.65/2.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 11.65/2.02      | r2_hidden(X1,k7_setfam_1(X1,X0)) = iProver_top
% 11.65/2.02      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_14,c_1158]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_30,plain,
% 11.65/2.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.65/2.02      inference(cnf_transformation,[],[f135]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1164,plain,
% 11.65/2.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_5955,plain,
% 11.65/2.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.65/2.02      | r2_hidden(X1,k7_setfam_1(X1,X0)) = iProver_top
% 11.65/2.02      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 11.65/2.02      inference(forward_subsumption_resolution,[status(thm)],[c_2012,c_1164]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_5961,plain,
% 11.65/2.02      ( r2_hidden(X0,k7_setfam_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = iProver_top
% 11.65/2.02      | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top
% 11.65/2.02      | r2_hidden(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_1162,c_5955]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_2,plain,
% 11.65/2.02      ( ~ r2_hidden(X0,X1)
% 11.65/2.02      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 11.65/2.02      inference(cnf_transformation,[],[f126]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1188,plain,
% 11.65/2.02      ( r2_hidden(X0,X1) != iProver_top
% 11.65/2.02      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_5090,plain,
% 11.65/2.02      ( r2_hidden(sK3,X0) != iProver_top | r1_tarski(sK4,X0) = iProver_top ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_40,c_1188]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_17589,plain,
% 11.65/2.02      ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
% 11.65/2.02      | r2_hidden(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
% 11.65/2.02      | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = iProver_top ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_5961,c_5090]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_17606,plain,
% 11.65/2.02      ( r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
% 11.65/2.02      | r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 11.65/2.02      | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_17589]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_30765,plain,
% 11.65/2.02      ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
% 11.65/2.02      | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top
% 11.65/2.02      | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_1162,c_30754]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_30819,plain,
% 11.65/2.02      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 11.65/2.02      | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
% 11.65/2.02      | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_30765]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_31639,plain,
% 11.65/2.02      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top ),
% 11.65/2.02      inference(global_propositional_subsumption,
% 11.65/2.02                [status(thm)],
% 11.65/2.02                [c_30769,c_41,c_39,c_120,c_1541,c_1999,c_2664,c_3288,c_3319,
% 11.65/2.02                 c_6098,c_8891,c_8993,c_17606,c_30819]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_13,plain,
% 11.65/2.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.65/2.02      inference(cnf_transformation,[],[f81]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1180,plain,
% 11.65/2.02      ( m1_subset_1(X0,X1) != iProver_top
% 11.65/2.02      | r2_hidden(X0,X1) = iProver_top
% 11.65/2.02      | v1_xboole_0(X1) = iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_3947,plain,
% 11.65/2.02      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
% 11.65/2.02      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 11.65/2.02      inference(superposition,[status(thm)],[c_1164,c_1180]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_31,plain,
% 11.65/2.02      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.65/2.02      inference(cnf_transformation,[],[f103]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_64,plain,
% 11.65/2.02      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_67,plain,
% 11.65/2.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1459,plain,
% 11.65/2.02      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 11.65/2.02      | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
% 11.65/2.02      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.65/2.02      inference(instantiation,[status(thm)],[c_13]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_1460,plain,
% 11.65/2.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 11.65/2.02      | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
% 11.65/2.02      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 11.65/2.02      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_8367,plain,
% 11.65/2.02      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.65/2.02      inference(global_propositional_subsumption,
% 11.65/2.02                [status(thm)],
% 11.65/2.02                [c_3947,c_64,c_67,c_1460]) ).
% 11.65/2.02  
% 11.65/2.02  cnf(c_31644,plain,
% 11.65/2.02      ( $false ),
% 11.65/2.02      inference(forward_subsumption_resolution,[status(thm)],[c_31639,c_8367]) ).
% 11.65/2.02  
% 11.65/2.02  
% 11.65/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.65/2.02  
% 11.65/2.02  ------                               Statistics
% 11.65/2.02  
% 11.65/2.02  ------ Selected
% 11.65/2.02  
% 11.65/2.02  total_time:                             1.319
% 11.65/2.02  
%------------------------------------------------------------------------------
