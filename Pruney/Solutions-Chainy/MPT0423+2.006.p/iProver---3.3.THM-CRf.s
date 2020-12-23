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

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 629 expanded)
%              Number of clauses        :   74 ( 101 expanded)
%              Number of leaves         :   31 ( 178 expanded)
%              Depth                    :   15
%              Number of atoms          :  359 ( 989 expanded)
%              Number of equality atoms :  218 ( 703 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

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

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f113])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f114])).

fof(f116,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f115])).

fof(f117,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f116])).

fof(f120,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f117])).

fof(f123,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f73,f120])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f133,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f101,f120])).

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

fof(f43,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f44,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f43])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f44,f61])).

fof(f110,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f62])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f41])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f50])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f80,f120,f120])).

fof(f137,plain,(
    ! [X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f128])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f76,f120])).

fof(f111,plain,(
    k1_tarski(sK3) = sK4 ),
    inference(cnf_transformation,[],[f62])).

fof(f135,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
    inference(definition_unfolding,[],[f111,f120])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f24,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f118,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f104,f117])).

fof(f119,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f64,f118])).

fof(f125,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f74,f119,f120,f120,f120])).

fof(f136,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f125])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f122,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f63,f118])).

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

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f38])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f78,f120,f120])).

fof(f112,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f134,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
    inference(definition_unfolding,[],[f112,f120])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f121,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f100,f81])).

fof(f131,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f82,f121])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f132,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f98,f81])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f120])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_28,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1089,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3118,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1089])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1081,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1087,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3498,plain,
    ( k7_setfam_1(sK3,k7_setfam_1(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_1081,c_1087])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1082,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_8566,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3498,c_1082])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1366,plain,
    ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1367,plain,
    ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1366])).

cnf(c_19593,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8566,c_39,c_1367])).

cnf(c_19607,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_19593])).

cnf(c_7,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_106,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_108,plain,
    ( r1_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1438,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1439,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1438])).

cnf(c_1441,plain,
    ( r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_367,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1818,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_37,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
    inference(cnf_transformation,[],[f135])).

cnf(c_4,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1261,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4,c_0,c_1])).

cnf(c_2656,plain,
    ( sK4 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_37,c_1261])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1792,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k7_setfam_1(X0,sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3292,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | k7_setfam_1(sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_368,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2007,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_3857,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_3858,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_3857])).

cnf(c_1586,plain,
    ( X0 != X1
    | k7_setfam_1(sK3,sK4) != X1
    | k7_setfam_1(sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_5774,plain,
    ( X0 != k7_setfam_1(sK3,sK4)
    | k7_setfam_1(sK3,sK4) = X0
    | k7_setfam_1(sK3,sK4) != k7_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_5776,plain,
    ( k7_setfam_1(sK3,sK4) != k7_setfam_1(sK3,sK4)
    | k7_setfam_1(sK3,sK4) = k1_xboole_0
    | k1_xboole_0 != k7_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_5774])).

cnf(c_5775,plain,
    ( k7_setfam_1(sK3,sK4) = k7_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_36,negated_conjecture,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_8664,plain,
    ( ~ r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_9,c_36])).

cnf(c_8665,plain,
    ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
    | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8664])).

cnf(c_10,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1084,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1964,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X1,k7_setfam_1(X1,X0)) = iProver_top
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1084])).

cnf(c_26,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_1091,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7322,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X1,k7_setfam_1(X1,X0)) = iProver_top
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1964,c_1091])).

cnf(c_7327,plain,
    ( r2_hidden(X0,k7_setfam_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = iProver_top
    | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1089,c_7322])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1111,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4792,plain,
    ( r2_hidden(sK3,X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_1111])).

cnf(c_15867,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7327,c_4792])).

cnf(c_15880,plain,
    ( r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_15867])).

cnf(c_19603,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1089,c_19593])).

cnf(c_19642,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19603])).

cnf(c_19833,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19607,c_38,c_108,c_1441,c_1818,c_2656,c_3292,c_3858,c_5776,c_5775,c_8665,c_15880,c_19642])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1086,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2280,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_1086])).

cnf(c_27,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_64,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_67,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1369,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1370,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_8078,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2280,c_64,c_67,c_1370])).

cnf(c_19838,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19833,c_8078])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.84/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.84/1.50  
% 7.84/1.50  ------  iProver source info
% 7.84/1.50  
% 7.84/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.84/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.84/1.50  git: non_committed_changes: false
% 7.84/1.50  git: last_make_outside_of_git: false
% 7.84/1.50  
% 7.84/1.50  ------ 
% 7.84/1.50  
% 7.84/1.50  ------ Input Options
% 7.84/1.50  
% 7.84/1.50  --out_options                           all
% 7.84/1.50  --tptp_safe_out                         true
% 7.84/1.50  --problem_path                          ""
% 7.84/1.50  --include_path                          ""
% 7.84/1.50  --clausifier                            res/vclausify_rel
% 7.84/1.50  --clausifier_options                    --mode clausify
% 7.84/1.50  --stdin                                 false
% 7.84/1.50  --stats_out                             sel
% 7.84/1.50  
% 7.84/1.50  ------ General Options
% 7.84/1.50  
% 7.84/1.50  --fof                                   false
% 7.84/1.50  --time_out_real                         604.99
% 7.84/1.50  --time_out_virtual                      -1.
% 7.84/1.50  --symbol_type_check                     false
% 7.84/1.50  --clausify_out                          false
% 7.84/1.50  --sig_cnt_out                           false
% 7.84/1.50  --trig_cnt_out                          false
% 7.84/1.50  --trig_cnt_out_tolerance                1.
% 7.84/1.50  --trig_cnt_out_sk_spl                   false
% 7.84/1.50  --abstr_cl_out                          false
% 7.84/1.50  
% 7.84/1.50  ------ Global Options
% 7.84/1.50  
% 7.84/1.50  --schedule                              none
% 7.84/1.50  --add_important_lit                     false
% 7.84/1.50  --prop_solver_per_cl                    1000
% 7.84/1.50  --min_unsat_core                        false
% 7.84/1.50  --soft_assumptions                      false
% 7.84/1.50  --soft_lemma_size                       3
% 7.84/1.50  --prop_impl_unit_size                   0
% 7.84/1.50  --prop_impl_unit                        []
% 7.84/1.50  --share_sel_clauses                     true
% 7.84/1.50  --reset_solvers                         false
% 7.84/1.50  --bc_imp_inh                            [conj_cone]
% 7.84/1.50  --conj_cone_tolerance                   3.
% 7.84/1.50  --extra_neg_conj                        none
% 7.84/1.50  --large_theory_mode                     true
% 7.84/1.50  --prolific_symb_bound                   200
% 7.84/1.50  --lt_threshold                          2000
% 7.84/1.50  --clause_weak_htbl                      true
% 7.84/1.50  --gc_record_bc_elim                     false
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing Options
% 7.84/1.50  
% 7.84/1.50  --preprocessing_flag                    true
% 7.84/1.50  --time_out_prep_mult                    0.1
% 7.84/1.50  --splitting_mode                        input
% 7.84/1.50  --splitting_grd                         true
% 7.84/1.50  --splitting_cvd                         false
% 7.84/1.50  --splitting_cvd_svl                     false
% 7.84/1.50  --splitting_nvd                         32
% 7.84/1.50  --sub_typing                            true
% 7.84/1.50  --prep_gs_sim                           false
% 7.84/1.50  --prep_unflatten                        true
% 7.84/1.50  --prep_res_sim                          true
% 7.84/1.50  --prep_upred                            true
% 7.84/1.50  --prep_sem_filter                       exhaustive
% 7.84/1.50  --prep_sem_filter_out                   false
% 7.84/1.50  --pred_elim                             false
% 7.84/1.50  --res_sim_input                         true
% 7.84/1.50  --eq_ax_congr_red                       true
% 7.84/1.50  --pure_diseq_elim                       true
% 7.84/1.50  --brand_transform                       false
% 7.84/1.50  --non_eq_to_eq                          false
% 7.84/1.50  --prep_def_merge                        true
% 7.84/1.50  --prep_def_merge_prop_impl              false
% 7.84/1.50  --prep_def_merge_mbd                    true
% 7.84/1.50  --prep_def_merge_tr_red                 false
% 7.84/1.50  --prep_def_merge_tr_cl                  false
% 7.84/1.50  --smt_preprocessing                     true
% 7.84/1.50  --smt_ac_axioms                         fast
% 7.84/1.50  --preprocessed_out                      false
% 7.84/1.50  --preprocessed_stats                    false
% 7.84/1.50  
% 7.84/1.50  ------ Abstraction refinement Options
% 7.84/1.50  
% 7.84/1.50  --abstr_ref                             []
% 7.84/1.50  --abstr_ref_prep                        false
% 7.84/1.50  --abstr_ref_until_sat                   false
% 7.84/1.50  --abstr_ref_sig_restrict                funpre
% 7.84/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.84/1.50  --abstr_ref_under                       []
% 7.84/1.50  
% 7.84/1.50  ------ SAT Options
% 7.84/1.50  
% 7.84/1.50  --sat_mode                              false
% 7.84/1.50  --sat_fm_restart_options                ""
% 7.84/1.50  --sat_gr_def                            false
% 7.84/1.50  --sat_epr_types                         true
% 7.84/1.50  --sat_non_cyclic_types                  false
% 7.84/1.50  --sat_finite_models                     false
% 7.84/1.50  --sat_fm_lemmas                         false
% 7.84/1.50  --sat_fm_prep                           false
% 7.84/1.50  --sat_fm_uc_incr                        true
% 7.84/1.50  --sat_out_model                         small
% 7.84/1.50  --sat_out_clauses                       false
% 7.84/1.50  
% 7.84/1.50  ------ QBF Options
% 7.84/1.50  
% 7.84/1.50  --qbf_mode                              false
% 7.84/1.50  --qbf_elim_univ                         false
% 7.84/1.50  --qbf_dom_inst                          none
% 7.84/1.50  --qbf_dom_pre_inst                      false
% 7.84/1.50  --qbf_sk_in                             false
% 7.84/1.50  --qbf_pred_elim                         true
% 7.84/1.50  --qbf_split                             512
% 7.84/1.50  
% 7.84/1.50  ------ BMC1 Options
% 7.84/1.50  
% 7.84/1.50  --bmc1_incremental                      false
% 7.84/1.50  --bmc1_axioms                           reachable_all
% 7.84/1.50  --bmc1_min_bound                        0
% 7.84/1.50  --bmc1_max_bound                        -1
% 7.84/1.50  --bmc1_max_bound_default                -1
% 7.84/1.50  --bmc1_symbol_reachability              true
% 7.84/1.50  --bmc1_property_lemmas                  false
% 7.84/1.50  --bmc1_k_induction                      false
% 7.84/1.50  --bmc1_non_equiv_states                 false
% 7.84/1.50  --bmc1_deadlock                         false
% 7.84/1.50  --bmc1_ucm                              false
% 7.84/1.50  --bmc1_add_unsat_core                   none
% 7.84/1.50  --bmc1_unsat_core_children              false
% 7.84/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.84/1.50  --bmc1_out_stat                         full
% 7.84/1.50  --bmc1_ground_init                      false
% 7.84/1.50  --bmc1_pre_inst_next_state              false
% 7.84/1.50  --bmc1_pre_inst_state                   false
% 7.84/1.50  --bmc1_pre_inst_reach_state             false
% 7.84/1.50  --bmc1_out_unsat_core                   false
% 7.84/1.50  --bmc1_aig_witness_out                  false
% 7.84/1.50  --bmc1_verbose                          false
% 7.84/1.50  --bmc1_dump_clauses_tptp                false
% 7.84/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.84/1.50  --bmc1_dump_file                        -
% 7.84/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.84/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.84/1.50  --bmc1_ucm_extend_mode                  1
% 7.84/1.50  --bmc1_ucm_init_mode                    2
% 7.84/1.50  --bmc1_ucm_cone_mode                    none
% 7.84/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.84/1.50  --bmc1_ucm_relax_model                  4
% 7.84/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.84/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.84/1.50  --bmc1_ucm_layered_model                none
% 7.84/1.50  --bmc1_ucm_max_lemma_size               10
% 7.84/1.50  
% 7.84/1.50  ------ AIG Options
% 7.84/1.50  
% 7.84/1.50  --aig_mode                              false
% 7.84/1.50  
% 7.84/1.50  ------ Instantiation Options
% 7.84/1.50  
% 7.84/1.50  --instantiation_flag                    true
% 7.84/1.50  --inst_sos_flag                         false
% 7.84/1.50  --inst_sos_phase                        true
% 7.84/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.84/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.84/1.50  --inst_lit_sel_side                     num_symb
% 7.84/1.50  --inst_solver_per_active                1400
% 7.84/1.50  --inst_solver_calls_frac                1.
% 7.84/1.50  --inst_passive_queue_type               priority_queues
% 7.84/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.84/1.50  --inst_passive_queues_freq              [25;2]
% 7.84/1.50  --inst_dismatching                      true
% 7.84/1.50  --inst_eager_unprocessed_to_passive     true
% 7.84/1.50  --inst_prop_sim_given                   true
% 7.84/1.50  --inst_prop_sim_new                     false
% 7.84/1.50  --inst_subs_new                         false
% 7.84/1.50  --inst_eq_res_simp                      false
% 7.84/1.50  --inst_subs_given                       false
% 7.84/1.50  --inst_orphan_elimination               true
% 7.84/1.50  --inst_learning_loop_flag               true
% 7.84/1.50  --inst_learning_start                   3000
% 7.84/1.50  --inst_learning_factor                  2
% 7.84/1.50  --inst_start_prop_sim_after_learn       3
% 7.84/1.50  --inst_sel_renew                        solver
% 7.84/1.50  --inst_lit_activity_flag                true
% 7.84/1.50  --inst_restr_to_given                   false
% 7.84/1.50  --inst_activity_threshold               500
% 7.84/1.50  --inst_out_proof                        true
% 7.84/1.50  
% 7.84/1.50  ------ Resolution Options
% 7.84/1.50  
% 7.84/1.50  --resolution_flag                       true
% 7.84/1.50  --res_lit_sel                           adaptive
% 7.84/1.50  --res_lit_sel_side                      none
% 7.84/1.50  --res_ordering                          kbo
% 7.84/1.50  --res_to_prop_solver                    active
% 7.84/1.50  --res_prop_simpl_new                    false
% 7.84/1.50  --res_prop_simpl_given                  true
% 7.84/1.50  --res_passive_queue_type                priority_queues
% 7.84/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.84/1.50  --res_passive_queues_freq               [15;5]
% 7.84/1.50  --res_forward_subs                      full
% 7.84/1.50  --res_backward_subs                     full
% 7.84/1.50  --res_forward_subs_resolution           true
% 7.84/1.50  --res_backward_subs_resolution          true
% 7.84/1.50  --res_orphan_elimination                true
% 7.84/1.50  --res_time_limit                        2.
% 7.84/1.50  --res_out_proof                         true
% 7.84/1.50  
% 7.84/1.50  ------ Superposition Options
% 7.84/1.50  
% 7.84/1.50  --superposition_flag                    true
% 7.84/1.50  --sup_passive_queue_type                priority_queues
% 7.84/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.84/1.50  --sup_passive_queues_freq               [1;4]
% 7.84/1.50  --demod_completeness_check              fast
% 7.84/1.50  --demod_use_ground                      true
% 7.84/1.50  --sup_to_prop_solver                    passive
% 7.84/1.50  --sup_prop_simpl_new                    true
% 7.84/1.50  --sup_prop_simpl_given                  true
% 7.84/1.50  --sup_fun_splitting                     false
% 7.84/1.50  --sup_smt_interval                      50000
% 7.84/1.50  
% 7.84/1.50  ------ Superposition Simplification Setup
% 7.84/1.50  
% 7.84/1.50  --sup_indices_passive                   []
% 7.84/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.84/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.84/1.50  --sup_full_bw                           [BwDemod]
% 7.84/1.50  --sup_immed_triv                        [TrivRules]
% 7.84/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.84/1.50  --sup_immed_bw_main                     []
% 7.84/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.84/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.84/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.84/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.84/1.50  
% 7.84/1.50  ------ Combination Options
% 7.84/1.50  
% 7.84/1.50  --comb_res_mult                         3
% 7.84/1.50  --comb_sup_mult                         2
% 7.84/1.50  --comb_inst_mult                        10
% 7.84/1.50  
% 7.84/1.50  ------ Debug Options
% 7.84/1.50  
% 7.84/1.50  --dbg_backtrace                         false
% 7.84/1.50  --dbg_dump_prop_clauses                 false
% 7.84/1.50  --dbg_dump_prop_clauses_file            -
% 7.84/1.50  --dbg_out_stat                          false
% 7.84/1.50  ------ Parsing...
% 7.84/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.84/1.50  ------ Proving...
% 7.84/1.50  ------ Problem Properties 
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  clauses                                 39
% 7.84/1.50  conjectures                             3
% 7.84/1.50  EPR                                     12
% 7.84/1.50  Horn                                    34
% 7.84/1.50  unary                                   21
% 7.84/1.50  binary                                  7
% 7.84/1.50  lits                                    77
% 7.84/1.50  lits eq                                 23
% 7.84/1.50  fd_pure                                 0
% 7.84/1.50  fd_pseudo                               0
% 7.84/1.50  fd_cond                                 1
% 7.84/1.50  fd_pseudo_cond                          4
% 7.84/1.50  AC symbols                              0
% 7.84/1.50  
% 7.84/1.50  ------ Input Options Time Limit: Unbounded
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  ------ 
% 7.84/1.50  Current options:
% 7.84/1.50  ------ 
% 7.84/1.50  
% 7.84/1.50  ------ Input Options
% 7.84/1.50  
% 7.84/1.50  --out_options                           all
% 7.84/1.50  --tptp_safe_out                         true
% 7.84/1.50  --problem_path                          ""
% 7.84/1.50  --include_path                          ""
% 7.84/1.50  --clausifier                            res/vclausify_rel
% 7.84/1.50  --clausifier_options                    --mode clausify
% 7.84/1.50  --stdin                                 false
% 7.84/1.50  --stats_out                             sel
% 7.84/1.50  
% 7.84/1.50  ------ General Options
% 7.84/1.50  
% 7.84/1.50  --fof                                   false
% 7.84/1.50  --time_out_real                         604.99
% 7.84/1.50  --time_out_virtual                      -1.
% 7.84/1.50  --symbol_type_check                     false
% 7.84/1.50  --clausify_out                          false
% 7.84/1.50  --sig_cnt_out                           false
% 7.84/1.50  --trig_cnt_out                          false
% 7.84/1.50  --trig_cnt_out_tolerance                1.
% 7.84/1.50  --trig_cnt_out_sk_spl                   false
% 7.84/1.50  --abstr_cl_out                          false
% 7.84/1.50  
% 7.84/1.50  ------ Global Options
% 7.84/1.50  
% 7.84/1.50  --schedule                              none
% 7.84/1.50  --add_important_lit                     false
% 7.84/1.50  --prop_solver_per_cl                    1000
% 7.84/1.50  --min_unsat_core                        false
% 7.84/1.50  --soft_assumptions                      false
% 7.84/1.50  --soft_lemma_size                       3
% 7.84/1.50  --prop_impl_unit_size                   0
% 7.84/1.50  --prop_impl_unit                        []
% 7.84/1.50  --share_sel_clauses                     true
% 7.84/1.50  --reset_solvers                         false
% 7.84/1.50  --bc_imp_inh                            [conj_cone]
% 7.84/1.50  --conj_cone_tolerance                   3.
% 7.84/1.50  --extra_neg_conj                        none
% 7.84/1.50  --large_theory_mode                     true
% 7.84/1.50  --prolific_symb_bound                   200
% 7.84/1.50  --lt_threshold                          2000
% 7.84/1.50  --clause_weak_htbl                      true
% 7.84/1.50  --gc_record_bc_elim                     false
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing Options
% 7.84/1.50  
% 7.84/1.50  --preprocessing_flag                    true
% 7.84/1.50  --time_out_prep_mult                    0.1
% 7.84/1.50  --splitting_mode                        input
% 7.84/1.50  --splitting_grd                         true
% 7.84/1.50  --splitting_cvd                         false
% 7.84/1.50  --splitting_cvd_svl                     false
% 7.84/1.50  --splitting_nvd                         32
% 7.84/1.50  --sub_typing                            true
% 7.84/1.50  --prep_gs_sim                           false
% 7.84/1.50  --prep_unflatten                        true
% 7.84/1.50  --prep_res_sim                          true
% 7.84/1.50  --prep_upred                            true
% 7.84/1.50  --prep_sem_filter                       exhaustive
% 7.84/1.50  --prep_sem_filter_out                   false
% 7.84/1.50  --pred_elim                             false
% 7.84/1.50  --res_sim_input                         true
% 7.84/1.50  --eq_ax_congr_red                       true
% 7.84/1.50  --pure_diseq_elim                       true
% 7.84/1.50  --brand_transform                       false
% 7.84/1.50  --non_eq_to_eq                          false
% 7.84/1.50  --prep_def_merge                        true
% 7.84/1.50  --prep_def_merge_prop_impl              false
% 7.84/1.50  --prep_def_merge_mbd                    true
% 7.84/1.50  --prep_def_merge_tr_red                 false
% 7.84/1.50  --prep_def_merge_tr_cl                  false
% 7.84/1.50  --smt_preprocessing                     true
% 7.84/1.50  --smt_ac_axioms                         fast
% 7.84/1.50  --preprocessed_out                      false
% 7.84/1.50  --preprocessed_stats                    false
% 7.84/1.50  
% 7.84/1.50  ------ Abstraction refinement Options
% 7.84/1.50  
% 7.84/1.50  --abstr_ref                             []
% 7.84/1.50  --abstr_ref_prep                        false
% 7.84/1.50  --abstr_ref_until_sat                   false
% 7.84/1.50  --abstr_ref_sig_restrict                funpre
% 7.84/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.84/1.50  --abstr_ref_under                       []
% 7.84/1.50  
% 7.84/1.50  ------ SAT Options
% 7.84/1.50  
% 7.84/1.50  --sat_mode                              false
% 7.84/1.50  --sat_fm_restart_options                ""
% 7.84/1.50  --sat_gr_def                            false
% 7.84/1.50  --sat_epr_types                         true
% 7.84/1.50  --sat_non_cyclic_types                  false
% 7.84/1.50  --sat_finite_models                     false
% 7.84/1.50  --sat_fm_lemmas                         false
% 7.84/1.50  --sat_fm_prep                           false
% 7.84/1.50  --sat_fm_uc_incr                        true
% 7.84/1.50  --sat_out_model                         small
% 7.84/1.50  --sat_out_clauses                       false
% 7.84/1.50  
% 7.84/1.50  ------ QBF Options
% 7.84/1.50  
% 7.84/1.50  --qbf_mode                              false
% 7.84/1.50  --qbf_elim_univ                         false
% 7.84/1.50  --qbf_dom_inst                          none
% 7.84/1.50  --qbf_dom_pre_inst                      false
% 7.84/1.50  --qbf_sk_in                             false
% 7.84/1.50  --qbf_pred_elim                         true
% 7.84/1.50  --qbf_split                             512
% 7.84/1.50  
% 7.84/1.50  ------ BMC1 Options
% 7.84/1.50  
% 7.84/1.50  --bmc1_incremental                      false
% 7.84/1.50  --bmc1_axioms                           reachable_all
% 7.84/1.50  --bmc1_min_bound                        0
% 7.84/1.50  --bmc1_max_bound                        -1
% 7.84/1.50  --bmc1_max_bound_default                -1
% 7.84/1.50  --bmc1_symbol_reachability              true
% 7.84/1.50  --bmc1_property_lemmas                  false
% 7.84/1.50  --bmc1_k_induction                      false
% 7.84/1.50  --bmc1_non_equiv_states                 false
% 7.84/1.50  --bmc1_deadlock                         false
% 7.84/1.50  --bmc1_ucm                              false
% 7.84/1.50  --bmc1_add_unsat_core                   none
% 7.84/1.50  --bmc1_unsat_core_children              false
% 7.84/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.84/1.50  --bmc1_out_stat                         full
% 7.84/1.50  --bmc1_ground_init                      false
% 7.84/1.50  --bmc1_pre_inst_next_state              false
% 7.84/1.50  --bmc1_pre_inst_state                   false
% 7.84/1.50  --bmc1_pre_inst_reach_state             false
% 7.84/1.50  --bmc1_out_unsat_core                   false
% 7.84/1.50  --bmc1_aig_witness_out                  false
% 7.84/1.50  --bmc1_verbose                          false
% 7.84/1.50  --bmc1_dump_clauses_tptp                false
% 7.84/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.84/1.50  --bmc1_dump_file                        -
% 7.84/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.84/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.84/1.50  --bmc1_ucm_extend_mode                  1
% 7.84/1.50  --bmc1_ucm_init_mode                    2
% 7.84/1.50  --bmc1_ucm_cone_mode                    none
% 7.84/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.84/1.50  --bmc1_ucm_relax_model                  4
% 7.84/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.84/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.84/1.50  --bmc1_ucm_layered_model                none
% 7.84/1.50  --bmc1_ucm_max_lemma_size               10
% 7.84/1.50  
% 7.84/1.50  ------ AIG Options
% 7.84/1.50  
% 7.84/1.50  --aig_mode                              false
% 7.84/1.50  
% 7.84/1.50  ------ Instantiation Options
% 7.84/1.50  
% 7.84/1.50  --instantiation_flag                    true
% 7.84/1.50  --inst_sos_flag                         false
% 7.84/1.50  --inst_sos_phase                        true
% 7.84/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.84/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.84/1.50  --inst_lit_sel_side                     num_symb
% 7.84/1.50  --inst_solver_per_active                1400
% 7.84/1.50  --inst_solver_calls_frac                1.
% 7.84/1.50  --inst_passive_queue_type               priority_queues
% 7.84/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.84/1.50  --inst_passive_queues_freq              [25;2]
% 7.84/1.50  --inst_dismatching                      true
% 7.84/1.50  --inst_eager_unprocessed_to_passive     true
% 7.84/1.50  --inst_prop_sim_given                   true
% 7.84/1.50  --inst_prop_sim_new                     false
% 7.84/1.50  --inst_subs_new                         false
% 7.84/1.50  --inst_eq_res_simp                      false
% 7.84/1.50  --inst_subs_given                       false
% 7.84/1.50  --inst_orphan_elimination               true
% 7.84/1.50  --inst_learning_loop_flag               true
% 7.84/1.50  --inst_learning_start                   3000
% 7.84/1.50  --inst_learning_factor                  2
% 7.84/1.50  --inst_start_prop_sim_after_learn       3
% 7.84/1.50  --inst_sel_renew                        solver
% 7.84/1.50  --inst_lit_activity_flag                true
% 7.84/1.50  --inst_restr_to_given                   false
% 7.84/1.50  --inst_activity_threshold               500
% 7.84/1.50  --inst_out_proof                        true
% 7.84/1.50  
% 7.84/1.50  ------ Resolution Options
% 7.84/1.50  
% 7.84/1.50  --resolution_flag                       true
% 7.84/1.50  --res_lit_sel                           adaptive
% 7.84/1.50  --res_lit_sel_side                      none
% 7.84/1.50  --res_ordering                          kbo
% 7.84/1.50  --res_to_prop_solver                    active
% 7.84/1.50  --res_prop_simpl_new                    false
% 7.84/1.50  --res_prop_simpl_given                  true
% 7.84/1.50  --res_passive_queue_type                priority_queues
% 7.84/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.84/1.50  --res_passive_queues_freq               [15;5]
% 7.84/1.50  --res_forward_subs                      full
% 7.84/1.50  --res_backward_subs                     full
% 7.84/1.50  --res_forward_subs_resolution           true
% 7.84/1.50  --res_backward_subs_resolution          true
% 7.84/1.50  --res_orphan_elimination                true
% 7.84/1.50  --res_time_limit                        2.
% 7.84/1.50  --res_out_proof                         true
% 7.84/1.50  
% 7.84/1.50  ------ Superposition Options
% 7.84/1.50  
% 7.84/1.50  --superposition_flag                    true
% 7.84/1.50  --sup_passive_queue_type                priority_queues
% 7.84/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.84/1.50  --sup_passive_queues_freq               [1;4]
% 7.84/1.50  --demod_completeness_check              fast
% 7.84/1.50  --demod_use_ground                      true
% 7.84/1.50  --sup_to_prop_solver                    passive
% 7.84/1.50  --sup_prop_simpl_new                    true
% 7.84/1.50  --sup_prop_simpl_given                  true
% 7.84/1.50  --sup_fun_splitting                     false
% 7.84/1.50  --sup_smt_interval                      50000
% 7.84/1.50  
% 7.84/1.50  ------ Superposition Simplification Setup
% 7.84/1.50  
% 7.84/1.50  --sup_indices_passive                   []
% 7.84/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.84/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.84/1.50  --sup_full_bw                           [BwDemod]
% 7.84/1.50  --sup_immed_triv                        [TrivRules]
% 7.84/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.84/1.50  --sup_immed_bw_main                     []
% 7.84/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.84/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.84/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.84/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.84/1.50  
% 7.84/1.50  ------ Combination Options
% 7.84/1.50  
% 7.84/1.50  --comb_res_mult                         3
% 7.84/1.50  --comb_sup_mult                         2
% 7.84/1.50  --comb_inst_mult                        10
% 7.84/1.50  
% 7.84/1.50  ------ Debug Options
% 7.84/1.50  
% 7.84/1.50  --dbg_backtrace                         false
% 7.84/1.50  --dbg_dump_prop_clauses                 false
% 7.84/1.50  --dbg_dump_prop_clauses_file            -
% 7.84/1.50  --dbg_out_stat                          false
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  ------ Proving...
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  % SZS status Theorem for theBenchmark.p
% 7.84/1.50  
% 7.84/1.50   Resolution empty clause
% 7.84/1.50  
% 7.84/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  fof(f11,axiom,(
% 7.84/1.50    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f73,plain,(
% 7.84/1.50    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.84/1.50    inference(cnf_transformation,[],[f11])).
% 7.84/1.50  
% 7.84/1.50  fof(f4,axiom,(
% 7.84/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f66,plain,(
% 7.84/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f4])).
% 7.84/1.50  
% 7.84/1.50  fof(f5,axiom,(
% 7.84/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f67,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f5])).
% 7.84/1.50  
% 7.84/1.50  fof(f6,axiom,(
% 7.84/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f68,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f6])).
% 7.84/1.50  
% 7.84/1.50  fof(f7,axiom,(
% 7.84/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f69,plain,(
% 7.84/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f7])).
% 7.84/1.50  
% 7.84/1.50  fof(f8,axiom,(
% 7.84/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f70,plain,(
% 7.84/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f8])).
% 7.84/1.50  
% 7.84/1.50  fof(f9,axiom,(
% 7.84/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f71,plain,(
% 7.84/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f9])).
% 7.84/1.50  
% 7.84/1.50  fof(f10,axiom,(
% 7.84/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f72,plain,(
% 7.84/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f10])).
% 7.84/1.50  
% 7.84/1.50  fof(f113,plain,(
% 7.84/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f71,f72])).
% 7.84/1.50  
% 7.84/1.50  fof(f114,plain,(
% 7.84/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f70,f113])).
% 7.84/1.50  
% 7.84/1.50  fof(f115,plain,(
% 7.84/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f69,f114])).
% 7.84/1.50  
% 7.84/1.50  fof(f116,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f68,f115])).
% 7.84/1.50  
% 7.84/1.50  fof(f117,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f67,f116])).
% 7.84/1.50  
% 7.84/1.50  fof(f120,plain,(
% 7.84/1.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f66,f117])).
% 7.84/1.50  
% 7.84/1.50  fof(f123,plain,(
% 7.84/1.50    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.84/1.50    inference(definition_unfolding,[],[f73,f120])).
% 7.84/1.50  
% 7.84/1.50  fof(f21,axiom,(
% 7.84/1.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f33,plain,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 7.84/1.50    inference(ennf_transformation,[],[f21])).
% 7.84/1.50  
% 7.84/1.50  fof(f101,plain,(
% 7.84/1.50    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f33])).
% 7.84/1.50  
% 7.84/1.50  fof(f133,plain,(
% 7.84/1.50    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f101,f120])).
% 7.84/1.50  
% 7.84/1.50  fof(f29,conjecture,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f30,negated_conjecture,(
% 7.84/1.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 7.84/1.50    inference(negated_conjecture,[],[f29])).
% 7.84/1.50  
% 7.84/1.50  fof(f43,plain,(
% 7.84/1.50    ? [X0,X1] : ((k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    inference(ennf_transformation,[],[f30])).
% 7.84/1.50  
% 7.84/1.50  fof(f44,plain,(
% 7.84/1.50    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    inference(flattening,[],[f43])).
% 7.84/1.50  
% 7.84/1.50  fof(f61,plain,(
% 7.84/1.50    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4) & k1_tarski(sK3) = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f62,plain,(
% 7.84/1.50    k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4) & k1_tarski(sK3) = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 7.84/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f44,f61])).
% 7.84/1.50  
% 7.84/1.50  fof(f110,plain,(
% 7.84/1.50    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 7.84/1.50    inference(cnf_transformation,[],[f62])).
% 7.84/1.50  
% 7.84/1.50  fof(f23,axiom,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f35,plain,(
% 7.84/1.50    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    inference(ennf_transformation,[],[f23])).
% 7.84/1.50  
% 7.84/1.50  fof(f103,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f35])).
% 7.84/1.50  
% 7.84/1.50  fof(f28,axiom,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f41,plain,(
% 7.84/1.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    inference(ennf_transformation,[],[f28])).
% 7.84/1.50  
% 7.84/1.50  fof(f42,plain,(
% 7.84/1.50    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    inference(flattening,[],[f41])).
% 7.84/1.50  
% 7.84/1.50  fof(f109,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f42])).
% 7.84/1.50  
% 7.84/1.50  fof(f22,axiom,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f34,plain,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    inference(ennf_transformation,[],[f22])).
% 7.84/1.50  
% 7.84/1.50  fof(f102,plain,(
% 7.84/1.50    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f34])).
% 7.84/1.50  
% 7.84/1.50  fof(f14,axiom,(
% 7.84/1.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f50,plain,(
% 7.84/1.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.84/1.50    inference(nnf_transformation,[],[f14])).
% 7.84/1.50  
% 7.84/1.50  fof(f51,plain,(
% 7.84/1.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.84/1.50    inference(flattening,[],[f50])).
% 7.84/1.50  
% 7.84/1.50  fof(f80,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 7.84/1.50    inference(cnf_transformation,[],[f51])).
% 7.84/1.50  
% 7.84/1.50  fof(f128,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 7.84/1.50    inference(definition_unfolding,[],[f80,f120,f120])).
% 7.84/1.50  
% 7.84/1.50  fof(f137,plain,(
% 7.84/1.50    ( ! [X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 7.84/1.50    inference(equality_resolution,[],[f128])).
% 7.84/1.50  
% 7.84/1.50  fof(f13,axiom,(
% 7.84/1.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f49,plain,(
% 7.84/1.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.84/1.50    inference(nnf_transformation,[],[f13])).
% 7.84/1.50  
% 7.84/1.50  fof(f76,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f49])).
% 7.84/1.50  
% 7.84/1.50  fof(f127,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f76,f120])).
% 7.84/1.50  
% 7.84/1.50  fof(f111,plain,(
% 7.84/1.50    k1_tarski(sK3) = sK4),
% 7.84/1.50    inference(cnf_transformation,[],[f62])).
% 7.84/1.50  
% 7.84/1.50  fof(f135,plain,(
% 7.84/1.50    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4),
% 7.84/1.50    inference(definition_unfolding,[],[f111,f120])).
% 7.84/1.50  
% 7.84/1.50  fof(f12,axiom,(
% 7.84/1.50    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f48,plain,(
% 7.84/1.50    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 7.84/1.50    inference(nnf_transformation,[],[f12])).
% 7.84/1.50  
% 7.84/1.50  fof(f74,plain,(
% 7.84/1.50    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f48])).
% 7.84/1.50  
% 7.84/1.50  fof(f2,axiom,(
% 7.84/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f64,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f2])).
% 7.84/1.50  
% 7.84/1.50  fof(f24,axiom,(
% 7.84/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f104,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f24])).
% 7.84/1.50  
% 7.84/1.50  fof(f118,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.84/1.50    inference(definition_unfolding,[],[f104,f117])).
% 7.84/1.50  
% 7.84/1.50  fof(f119,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.84/1.50    inference(definition_unfolding,[],[f64,f118])).
% 7.84/1.50  
% 7.84/1.50  fof(f125,plain,(
% 7.84/1.50    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f74,f119,f120,f120,f120])).
% 7.84/1.50  
% 7.84/1.50  fof(f136,plain,(
% 7.84/1.50    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 7.84/1.50    inference(equality_resolution,[],[f125])).
% 7.84/1.50  
% 7.84/1.50  fof(f1,axiom,(
% 7.84/1.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f31,plain,(
% 7.84/1.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.84/1.50    inference(rectify,[],[f1])).
% 7.84/1.50  
% 7.84/1.50  fof(f63,plain,(
% 7.84/1.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.84/1.50    inference(cnf_transformation,[],[f31])).
% 7.84/1.50  
% 7.84/1.50  fof(f122,plain,(
% 7.84/1.50    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 7.84/1.50    inference(definition_unfolding,[],[f63,f118])).
% 7.84/1.50  
% 7.84/1.50  fof(f3,axiom,(
% 7.84/1.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f65,plain,(
% 7.84/1.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.84/1.50    inference(cnf_transformation,[],[f3])).
% 7.84/1.50  
% 7.84/1.50  fof(f26,axiom,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f38,plain,(
% 7.84/1.50    ! [X0,X1] : ((k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    inference(ennf_transformation,[],[f26])).
% 7.84/1.50  
% 7.84/1.50  fof(f39,plain,(
% 7.84/1.50    ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    inference(flattening,[],[f38])).
% 7.84/1.50  
% 7.84/1.50  fof(f106,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f39])).
% 7.84/1.50  
% 7.84/1.50  fof(f78,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f51])).
% 7.84/1.50  
% 7.84/1.50  fof(f130,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 7.84/1.50    inference(definition_unfolding,[],[f78,f120,f120])).
% 7.84/1.50  
% 7.84/1.50  fof(f112,plain,(
% 7.84/1.50    k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4)),
% 7.84/1.50    inference(cnf_transformation,[],[f62])).
% 7.84/1.50  
% 7.84/1.50  fof(f134,plain,(
% 7.84/1.50    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4)),
% 7.84/1.50    inference(definition_unfolding,[],[f112,f120])).
% 7.84/1.50  
% 7.84/1.50  fof(f16,axiom,(
% 7.84/1.50    ! [X0] : k2_subset_1(X0) = X0),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f82,plain,(
% 7.84/1.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.84/1.50    inference(cnf_transformation,[],[f16])).
% 7.84/1.50  
% 7.84/1.50  fof(f20,axiom,(
% 7.84/1.50    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f100,plain,(
% 7.84/1.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f20])).
% 7.84/1.50  
% 7.84/1.50  fof(f15,axiom,(
% 7.84/1.50    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f81,plain,(
% 7.84/1.50    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f15])).
% 7.84/1.50  
% 7.84/1.50  fof(f121,plain,(
% 7.84/1.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f100,f81])).
% 7.84/1.50  
% 7.84/1.50  fof(f131,plain,(
% 7.84/1.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 7.84/1.50    inference(definition_unfolding,[],[f82,f121])).
% 7.84/1.50  
% 7.84/1.50  fof(f27,axiom,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f40,plain,(
% 7.84/1.50    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    inference(ennf_transformation,[],[f27])).
% 7.84/1.50  
% 7.84/1.50  fof(f60,plain,(
% 7.84/1.50    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.50    inference(nnf_transformation,[],[f40])).
% 7.84/1.50  
% 7.84/1.50  fof(f108,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f60])).
% 7.84/1.50  
% 7.84/1.50  fof(f18,axiom,(
% 7.84/1.50    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f98,plain,(
% 7.84/1.50    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f18])).
% 7.84/1.50  
% 7.84/1.50  fof(f132,plain,(
% 7.84/1.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.84/1.50    inference(definition_unfolding,[],[f98,f81])).
% 7.84/1.50  
% 7.84/1.50  fof(f77,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f49])).
% 7.84/1.50  
% 7.84/1.50  fof(f126,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f77,f120])).
% 7.84/1.50  
% 7.84/1.50  fof(f25,axiom,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f36,plain,(
% 7.84/1.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.84/1.50    inference(ennf_transformation,[],[f25])).
% 7.84/1.50  
% 7.84/1.50  fof(f37,plain,(
% 7.84/1.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.84/1.50    inference(flattening,[],[f36])).
% 7.84/1.50  
% 7.84/1.50  fof(f105,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f37])).
% 7.84/1.50  
% 7.84/1.50  fof(f19,axiom,(
% 7.84/1.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f99,plain,(
% 7.84/1.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f19])).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2,plain,
% 7.84/1.50      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f123]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_28,plain,
% 7.84/1.50      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
% 7.84/1.50      | ~ r2_hidden(X0,X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f133]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1089,plain,
% 7.84/1.50      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 7.84/1.50      | r2_hidden(X0,X1) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3118,plain,
% 7.84/1.50      ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 7.84/1.50      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2,c_1089]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_38,negated_conjecture,
% 7.84/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 7.84/1.50      inference(cnf_transformation,[],[f110]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1081,plain,
% 7.84/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_30,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.84/1.50      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 7.84/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1087,plain,
% 7.84/1.50      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 7.84/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3498,plain,
% 7.84/1.50      ( k7_setfam_1(sK3,k7_setfam_1(sK3,sK4)) = sK4 ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_1081,c_1087]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_35,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.84/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.84/1.50      | r1_tarski(X0,X2)
% 7.84/1.50      | ~ r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 7.84/1.50      inference(cnf_transformation,[],[f109]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1082,plain,
% 7.84/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.84/1.50      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.84/1.50      | r1_tarski(X0,X2) = iProver_top
% 7.84/1.50      | r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_8566,plain,
% 7.84/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 7.84/1.50      | m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 7.84/1.50      | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
% 7.84/1.50      | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_3498,c_1082]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_39,plain,
% 7.84/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_29,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.84/1.50      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 7.84/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1366,plain,
% 7.84/1.50      ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3)))
% 7.84/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_29]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1367,plain,
% 7.84/1.50      ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top
% 7.84/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_1366]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19593,plain,
% 7.84/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 7.84/1.50      | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
% 7.84/1.50      | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_8566,c_39,c_1367]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19607,plain,
% 7.84/1.50      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 7.84/1.50      | r1_tarski(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.84/1.50      | r1_tarski(sK4,k7_setfam_1(sK3,k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_3118,c_19593]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_7,plain,
% 7.84/1.50      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.84/1.50      inference(cnf_transformation,[],[f137]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_106,plain,
% 7.84/1.50      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_108,plain,
% 7.84/1.50      ( r1_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_106]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_6,plain,
% 7.84/1.50      ( r2_hidden(X0,X1)
% 7.84/1.50      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f127]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1438,plain,
% 7.84/1.50      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.84/1.50      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1439,plain,
% 7.84/1.50      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top
% 7.84/1.50      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_1438]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1441,plain,
% 7.84/1.50      ( r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
% 7.84/1.50      | r1_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_1439]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_367,plain,( X0 = X0 ),theory(equality) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1818,plain,
% 7.84/1.50      ( sK4 = sK4 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_367]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_37,negated_conjecture,
% 7.84/1.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
% 7.84/1.50      inference(cnf_transformation,[],[f135]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4,plain,
% 7.84/1.50      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f136]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_0,plain,
% 7.84/1.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 7.84/1.50      inference(cnf_transformation,[],[f122]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1,plain,
% 7.84/1.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.84/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1261,plain,
% 7.84/1.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 7.84/1.50      inference(demodulation,[status(thm)],[c_4,c_0,c_1]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2656,plain,
% 7.84/1.50      ( sK4 != k1_xboole_0 ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_37,c_1261]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_32,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.84/1.50      | k7_setfam_1(X1,X0) != k1_xboole_0
% 7.84/1.50      | k1_xboole_0 = X0 ),
% 7.84/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1792,plain,
% 7.84/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 7.84/1.50      | k7_setfam_1(X0,sK4) != k1_xboole_0
% 7.84/1.50      | k1_xboole_0 = sK4 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_32]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3292,plain,
% 7.84/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))
% 7.84/1.50      | k7_setfam_1(sK3,sK4) != k1_xboole_0
% 7.84/1.50      | k1_xboole_0 = sK4 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_1792]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_368,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2007,plain,
% 7.84/1.50      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_368]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3857,plain,
% 7.84/1.50      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_2007]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3858,plain,
% 7.84/1.50      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3857]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1586,plain,
% 7.84/1.50      ( X0 != X1 | k7_setfam_1(sK3,sK4) != X1 | k7_setfam_1(sK3,sK4) = X0 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_368]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_5774,plain,
% 7.84/1.50      ( X0 != k7_setfam_1(sK3,sK4)
% 7.84/1.50      | k7_setfam_1(sK3,sK4) = X0
% 7.84/1.50      | k7_setfam_1(sK3,sK4) != k7_setfam_1(sK3,sK4) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_1586]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_5776,plain,
% 7.84/1.50      ( k7_setfam_1(sK3,sK4) != k7_setfam_1(sK3,sK4)
% 7.84/1.50      | k7_setfam_1(sK3,sK4) = k1_xboole_0
% 7.84/1.50      | k1_xboole_0 != k7_setfam_1(sK3,sK4) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_5774]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_5775,plain,
% 7.84/1.50      ( k7_setfam_1(sK3,sK4) = k7_setfam_1(sK3,sK4) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_367]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_9,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 7.84/1.50      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 7.84/1.50      | k1_xboole_0 = X0 ),
% 7.84/1.50      inference(cnf_transformation,[],[f130]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_36,negated_conjecture,
% 7.84/1.50      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
% 7.84/1.50      inference(cnf_transformation,[],[f134]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_8664,plain,
% 7.84/1.50      ( ~ r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.84/1.50      | k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_9,c_36]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_8665,plain,
% 7.84/1.50      ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
% 7.84/1.50      | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_8664]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_10,plain,
% 7.84/1.50      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 7.84/1.50      inference(cnf_transformation,[],[f131]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_33,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.84/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.84/1.50      | ~ r2_hidden(X0,X2)
% 7.84/1.50      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 7.84/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1084,plain,
% 7.84/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.84/1.50      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.84/1.50      | r2_hidden(X0,X2) != iProver_top
% 7.84/1.50      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1964,plain,
% 7.84/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.84/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 7.84/1.50      | r2_hidden(X1,k7_setfam_1(X1,X0)) = iProver_top
% 7.84/1.50      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_10,c_1084]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_26,plain,
% 7.84/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.84/1.50      inference(cnf_transformation,[],[f132]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1091,plain,
% 7.84/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_7322,plain,
% 7.84/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.84/1.50      | r2_hidden(X1,k7_setfam_1(X1,X0)) = iProver_top
% 7.84/1.50      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 7.84/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_1964,c_1091]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_7327,plain,
% 7.84/1.50      ( r2_hidden(X0,k7_setfam_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = iProver_top
% 7.84/1.50      | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.84/1.50      | r2_hidden(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_1089,c_7322]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_5,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,X1)
% 7.84/1.50      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f126]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1111,plain,
% 7.84/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.84/1.50      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4792,plain,
% 7.84/1.50      ( r2_hidden(sK3,X0) != iProver_top | r1_tarski(sK4,X0) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_37,c_1111]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_15867,plain,
% 7.84/1.50      ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
% 7.84/1.50      | r2_hidden(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
% 7.84/1.50      | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_7327,c_4792]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_15880,plain,
% 7.84/1.50      ( r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.84/1.50      | r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 7.84/1.50      | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_15867]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19603,plain,
% 7.84/1.50      ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
% 7.84/1.50      | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top
% 7.84/1.50      | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_1089,c_19593]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19642,plain,
% 7.84/1.50      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 7.84/1.50      | r1_tarski(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
% 7.84/1.50      | r1_tarski(sK4,k7_setfam_1(sK3,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_19603]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19833,plain,
% 7.84/1.50      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_19607,c_38,c_108,c_1441,c_1818,c_2656,c_3292,c_3858,
% 7.84/1.50                 c_5776,c_5775,c_8665,c_15880,c_19642]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_31,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1086,plain,
% 7.84/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.84/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.84/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2280,plain,
% 7.84/1.50      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
% 7.84/1.50      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_1091,c_1086]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_27,plain,
% 7.84/1.50      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.84/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_64,plain,
% 7.84/1.50      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_67,plain,
% 7.84/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1369,plain,
% 7.84/1.50      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 7.84/1.50      | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
% 7.84/1.50      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_31]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1370,plain,
% 7.84/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 7.84/1.50      | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
% 7.84/1.50      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_8078,plain,
% 7.84/1.50      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_2280,c_64,c_67,c_1370]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19838,plain,
% 7.84/1.50      ( $false ),
% 7.84/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_19833,c_8078]) ).
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  ------                               Statistics
% 7.84/1.50  
% 7.84/1.50  ------ Selected
% 7.84/1.50  
% 7.84/1.50  total_time:                             0.915
% 7.84/1.50  
%------------------------------------------------------------------------------
