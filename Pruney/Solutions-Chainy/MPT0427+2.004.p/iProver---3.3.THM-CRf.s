%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:27 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  161 (1377 expanded)
%              Number of clauses        :   87 ( 464 expanded)
%              Number of leaves         :   24 ( 338 expanded)
%              Depth                    :   27
%              Number of atoms          :  337 (4034 expanded)
%              Number of equality atoms :  195 (1270 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f49])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X0))))) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2))
          & r1_tarski(sK2,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f39,f38])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k1_tarski(X0),k1_setfam_1(k1_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X1)))) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f74,plain,(
    ! [X1] : k5_xboole_0(k1_tarski(X1),k1_setfam_1(k1_enumset1(k1_tarski(X1),k1_tarski(X1),k1_tarski(X1)))) != k1_tarski(X1) ),
    inference(equality_resolution,[],[f73])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_setfam_1(k1_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X1)))) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f52,f67])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_xboole_0(X0,X1)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))) ) ),
    inference(definition_unfolding,[],[f46,f68])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_600,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X0))))) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_597,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X0))))) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2801,plain,
    ( k5_xboole_0(k1_tarski(sK0(X0)),k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_tarski(sK0(X0)))))) = X0
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_600,c_597])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_590,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_587,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_595,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2593,plain,
    ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_587,c_595])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_593,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1991,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_587,c_593])).

cnf(c_2602,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2593,c_1991])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_586,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2594,plain,
    ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_586,c_595])).

cnf(c_1992,plain,
    ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_586,c_593])).

cnf(c_2597,plain,
    ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2594,c_1992])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_589,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3176,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2597,c_589])).

cnf(c_3257,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2602,c_3176])).

cnf(c_3779,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_590,c_3257])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3782,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3779,c_23])).

cnf(c_3783,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3782])).

cnf(c_3795,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3783,c_586])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( k5_xboole_0(k1_tarski(X0),k1_setfam_1(k1_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0)))) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_47,plain,
    ( k5_xboole_0(k1_tarski(k1_xboole_0),k1_setfam_1(k1_enumset1(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)))) != k1_tarski(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( X0 = X1
    | k5_xboole_0(k1_tarski(X1),k1_setfam_1(k1_enumset1(k1_tarski(X1),k1_tarski(X1),k1_tarski(X0)))) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_48,plain,
    ( k5_xboole_0(k1_tarski(k1_xboole_0),k1_setfam_1(k1_enumset1(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)))) = k1_tarski(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_201,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_884,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_885,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_207,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_772,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | X1 != k1_zfmisc_1(k1_zfmisc_1(sK1))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_1001,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | X0 != sK3
    | k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_1003,plain,
    ( X0 != sK3
    | k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1001])).

cnf(c_1005,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
    | k1_xboole_0 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_200,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1002,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK1)) = k1_zfmisc_1(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_4173,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3795,c_22,c_47,c_48,c_885,c_1005,c_1002])).

cnf(c_10,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_596,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4179,plain,
    ( k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_4173,c_596])).

cnf(c_3794,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3783,c_589])).

cnf(c_4197,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4179,c_3794])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_735,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_736,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_844,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),sK1)
    | ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_845,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top
    | m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_844])).

cnf(c_5074,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4197,c_22,c_736,c_845])).

cnf(c_588,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_123,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_153,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_123])).

cnf(c_585,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_153])).

cnf(c_1031,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_585])).

cnf(c_5085,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5074,c_1031])).

cnf(c_5515,plain,
    ( k5_xboole_0(k1_tarski(sK0(k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_tarski(sK0(k1_xboole_0)))))) = k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_5085])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_598,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7118,plain,
    ( k5_xboole_0(k1_tarski(sK0(k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_tarski(sK0(k1_xboole_0)))))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5515,c_598])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7396,plain,
    ( k1_tarski(sK0(k1_xboole_0)) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7118,c_4])).

cnf(c_2,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_641,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8,c_2,c_5])).

cnf(c_7399,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7396,c_641])).

cnf(c_5086,plain,
    ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5074,c_589])).

cnf(c_5092,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5086,c_4179])).

cnf(c_7407,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7399,c_5092])).

cnf(c_7419,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7407,c_4179])).

cnf(c_594,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_591,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2186,plain,
    ( r1_tarski(k8_setfam_1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_591])).

cnf(c_4181,plain,
    ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4173,c_2186])).

cnf(c_4188,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4179,c_4181])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7419,c_4188])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:44:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.92/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/0.97  
% 3.92/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/0.97  
% 3.92/0.97  ------  iProver source info
% 3.92/0.97  
% 3.92/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.92/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/0.97  git: non_committed_changes: false
% 3.92/0.97  git: last_make_outside_of_git: false
% 3.92/0.97  
% 3.92/0.97  ------ 
% 3.92/0.97  ------ Parsing...
% 3.92/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/0.97  
% 3.92/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.92/0.97  
% 3.92/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/0.97  
% 3.92/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.97  ------ Proving...
% 3.92/0.97  ------ Problem Properties 
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  clauses                                 21
% 3.92/0.97  conjectures                             4
% 3.92/0.97  EPR                                     4
% 3.92/0.97  Horn                                    17
% 3.92/0.97  unary                                   7
% 3.92/0.97  binary                                  11
% 3.92/0.97  lits                                    38
% 3.92/0.97  lits eq                                 14
% 3.92/0.97  fd_pure                                 0
% 3.92/0.97  fd_pseudo                               0
% 3.92/0.97  fd_cond                                 4
% 3.92/0.97  fd_pseudo_cond                          1
% 3.92/0.97  AC symbols                              0
% 3.92/0.97  
% 3.92/0.97  ------ Input Options Time Limit: Unbounded
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  ------ 
% 3.92/0.97  Current options:
% 3.92/0.97  ------ 
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  ------ Proving...
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  % SZS status Theorem for theBenchmark.p
% 3.92/0.97  
% 3.92/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.92/0.97  
% 3.92/0.97  fof(f1,axiom,(
% 3.92/0.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f32,plain,(
% 3.92/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.92/0.97    inference(nnf_transformation,[],[f1])).
% 3.92/0.97  
% 3.92/0.97  fof(f33,plain,(
% 3.92/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.92/0.97    inference(rectify,[],[f32])).
% 3.92/0.97  
% 3.92/0.97  fof(f34,plain,(
% 3.92/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.92/0.97    introduced(choice_axiom,[])).
% 3.92/0.97  
% 3.92/0.97  fof(f35,plain,(
% 3.92/0.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.92/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.92/0.97  
% 3.92/0.97  fof(f42,plain,(
% 3.92/0.97    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.92/0.97    inference(cnf_transformation,[],[f35])).
% 3.92/0.97  
% 3.92/0.97  fof(f9,axiom,(
% 3.92/0.97    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f23,plain,(
% 3.92/0.97    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 3.92/0.97    inference(ennf_transformation,[],[f9])).
% 3.92/0.97  
% 3.92/0.97  fof(f50,plain,(
% 3.92/0.97    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.92/0.97    inference(cnf_transformation,[],[f23])).
% 3.92/0.97  
% 3.92/0.97  fof(f7,axiom,(
% 3.92/0.97    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f48,plain,(
% 3.92/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.92/0.97    inference(cnf_transformation,[],[f7])).
% 3.92/0.97  
% 3.92/0.97  fof(f4,axiom,(
% 3.92/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f45,plain,(
% 3.92/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.92/0.97    inference(cnf_transformation,[],[f4])).
% 3.92/0.97  
% 3.92/0.97  fof(f15,axiom,(
% 3.92/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f58,plain,(
% 3.92/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.92/0.97    inference(cnf_transformation,[],[f15])).
% 3.92/0.97  
% 3.92/0.97  fof(f8,axiom,(
% 3.92/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f49,plain,(
% 3.92/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.92/0.97    inference(cnf_transformation,[],[f8])).
% 3.92/0.97  
% 3.92/0.97  fof(f66,plain,(
% 3.92/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.92/0.97    inference(definition_unfolding,[],[f58,f49])).
% 3.92/0.97  
% 3.92/0.97  fof(f67,plain,(
% 3.92/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.92/0.97    inference(definition_unfolding,[],[f45,f66])).
% 3.92/0.97  
% 3.92/0.97  fof(f68,plain,(
% 3.92/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 3.92/0.97    inference(definition_unfolding,[],[f48,f67])).
% 3.92/0.97  
% 3.92/0.97  fof(f71,plain,(
% 3.92/0.97    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X0))))) = X1 | ~r2_hidden(X0,X1)) )),
% 3.92/0.97    inference(definition_unfolding,[],[f50,f68])).
% 3.92/0.97  
% 3.92/0.97  fof(f17,axiom,(
% 3.92/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 3.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f28,plain,(
% 3.92/0.97    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 3.92/0.97    inference(ennf_transformation,[],[f17])).
% 3.92/0.97  
% 3.92/0.97  fof(f29,plain,(
% 3.92/0.97    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 3.92/0.97    inference(flattening,[],[f28])).
% 3.92/0.97  
% 3.92/0.97  fof(f61,plain,(
% 3.92/0.97    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 3.92/0.97    inference(cnf_transformation,[],[f29])).
% 3.92/0.97  
% 3.92/0.97  fof(f18,conjecture,(
% 3.92/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 3.92/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f19,negated_conjecture,(
% 3.92/0.97    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 3.92/0.97    inference(negated_conjecture,[],[f18])).
% 3.92/0.97  
% 3.92/0.97  fof(f30,plain,(
% 3.92/0.97    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.92/0.97    inference(ennf_transformation,[],[f19])).
% 3.92/0.97  
% 3.92/0.97  fof(f31,plain,(
% 3.92/0.97    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.92/0.97    inference(flattening,[],[f30])).
% 3.92/0.97  
% 3.92/0.97  fof(f39,plain,(
% 3.92/0.97    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 3.92/0.97    introduced(choice_axiom,[])).
% 3.92/0.97  
% 3.92/0.97  fof(f38,plain,(
% 3.92/0.97    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 3.92/0.97    introduced(choice_axiom,[])).
% 3.92/0.97  
% 3.92/0.97  fof(f40,plain,(
% 3.92/0.97    (~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.92/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f39,f38])).
% 3.92/0.98  
% 3.92/0.98  fof(f63,plain,(
% 3.92/0.98    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.92/0.98    inference(cnf_transformation,[],[f40])).
% 3.92/0.98  
% 3.92/0.98  fof(f12,axiom,(
% 3.92/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 3.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f25,plain,(
% 3.92/0.98    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.92/0.98    inference(ennf_transformation,[],[f12])).
% 3.92/0.98  
% 3.92/0.98  fof(f54,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.92/0.98    inference(cnf_transformation,[],[f25])).
% 3.92/0.98  
% 3.92/0.98  fof(f14,axiom,(
% 3.92/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 3.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f27,plain,(
% 3.92/0.98    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.92/0.98    inference(ennf_transformation,[],[f14])).
% 3.92/0.98  
% 3.92/0.98  fof(f57,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.92/0.98    inference(cnf_transformation,[],[f27])).
% 3.92/0.98  
% 3.92/0.98  fof(f62,plain,(
% 3.92/0.98    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.92/0.98    inference(cnf_transformation,[],[f40])).
% 3.92/0.98  
% 3.92/0.98  fof(f65,plain,(
% 3.92/0.98    ~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))),
% 3.92/0.98    inference(cnf_transformation,[],[f40])).
% 3.92/0.98  
% 3.92/0.98  fof(f64,plain,(
% 3.92/0.98    r1_tarski(sK2,sK3)),
% 3.92/0.98    inference(cnf_transformation,[],[f40])).
% 3.92/0.98  
% 3.92/0.98  fof(f10,axiom,(
% 3.92/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f36,plain,(
% 3.92/0.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.92/0.98    inference(nnf_transformation,[],[f10])).
% 3.92/0.98  
% 3.92/0.98  fof(f51,plain,(
% 3.92/0.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f36])).
% 3.92/0.98  
% 3.92/0.98  fof(f73,plain,(
% 3.92/0.98    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k1_tarski(X0),k1_setfam_1(k1_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X1)))) != k1_tarski(X0)) )),
% 3.92/0.98    inference(definition_unfolding,[],[f51,f67])).
% 3.92/0.98  
% 3.92/0.98  fof(f74,plain,(
% 3.92/0.98    ( ! [X1] : (k5_xboole_0(k1_tarski(X1),k1_setfam_1(k1_enumset1(k1_tarski(X1),k1_tarski(X1),k1_tarski(X1)))) != k1_tarski(X1)) )),
% 3.92/0.98    inference(equality_resolution,[],[f73])).
% 3.92/0.98  
% 3.92/0.98  fof(f52,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.92/0.98    inference(cnf_transformation,[],[f36])).
% 3.92/0.98  
% 3.92/0.98  fof(f72,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_setfam_1(k1_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X1)))) = k1_tarski(X0) | X0 = X1) )),
% 3.92/0.98    inference(definition_unfolding,[],[f52,f67])).
% 3.92/0.98  
% 3.92/0.98  fof(f55,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.92/0.98    inference(cnf_transformation,[],[f25])).
% 3.92/0.98  
% 3.92/0.98  fof(f75,plain,(
% 3.92/0.98    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.92/0.98    inference(equality_resolution,[],[f55])).
% 3.92/0.98  
% 3.92/0.98  fof(f13,axiom,(
% 3.92/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f26,plain,(
% 3.92/0.98    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.92/0.98    inference(ennf_transformation,[],[f13])).
% 3.92/0.98  
% 3.92/0.98  fof(f56,plain,(
% 3.92/0.98    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.92/0.98    inference(cnf_transformation,[],[f26])).
% 3.92/0.98  
% 3.92/0.98  fof(f16,axiom,(
% 3.92/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f37,plain,(
% 3.92/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.92/0.98    inference(nnf_transformation,[],[f16])).
% 3.92/0.98  
% 3.92/0.98  fof(f59,plain,(
% 3.92/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.92/0.98    inference(cnf_transformation,[],[f37])).
% 3.92/0.98  
% 3.92/0.98  fof(f11,axiom,(
% 3.92/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f24,plain,(
% 3.92/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.92/0.98    inference(ennf_transformation,[],[f11])).
% 3.92/0.98  
% 3.92/0.98  fof(f53,plain,(
% 3.92/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f24])).
% 3.92/0.98  
% 3.92/0.98  fof(f60,plain,(
% 3.92/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f37])).
% 3.92/0.98  
% 3.92/0.98  fof(f3,axiom,(
% 3.92/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f21,plain,(
% 3.92/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.92/0.98    inference(ennf_transformation,[],[f3])).
% 3.92/0.98  
% 3.92/0.98  fof(f44,plain,(
% 3.92/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f21])).
% 3.92/0.98  
% 3.92/0.98  fof(f5,axiom,(
% 3.92/0.98    ! [X0,X1] : (k1_xboole_0 = k2_xboole_0(X0,X1) => k1_xboole_0 = X0)),
% 3.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f22,plain,(
% 3.92/0.98    ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_xboole_0(X0,X1))),
% 3.92/0.98    inference(ennf_transformation,[],[f5])).
% 3.92/0.98  
% 3.92/0.98  fof(f46,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_xboole_0(X0,X1)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f22])).
% 3.92/0.98  
% 3.92/0.98  fof(f70,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0))))) )),
% 3.92/0.98    inference(definition_unfolding,[],[f46,f68])).
% 3.92/0.98  
% 3.92/0.98  fof(f2,axiom,(
% 3.92/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f20,plain,(
% 3.92/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.92/0.98    inference(rectify,[],[f2])).
% 3.92/0.98  
% 3.92/0.98  fof(f43,plain,(
% 3.92/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.92/0.98    inference(cnf_transformation,[],[f20])).
% 3.92/0.98  
% 3.92/0.98  fof(f69,plain,(
% 3.92/0.98    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 3.92/0.98    inference(definition_unfolding,[],[f43,f66])).
% 3.92/0.98  
% 3.92/0.98  fof(f6,axiom,(
% 3.92/0.98    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f47,plain,(
% 3.92/0.98    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f6])).
% 3.92/0.98  
% 3.92/0.98  cnf(c_0,plain,
% 3.92/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.92/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_600,plain,
% 3.92/0.98      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.92/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_6,plain,
% 3.92/0.98      ( ~ r2_hidden(X0,X1)
% 3.92/0.98      | k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X0))))) = X1 ),
% 3.92/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_597,plain,
% 3.92/0.98      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X0))))) = X1
% 3.92/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2801,plain,
% 3.92/0.98      ( k5_xboole_0(k1_tarski(sK0(X0)),k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_tarski(sK0(X0)))))) = X0
% 3.92/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_600,c_597]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_16,plain,
% 3.92/0.98      ( ~ r1_tarski(X0,X1)
% 3.92/0.98      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 3.92/0.98      | k1_xboole_0 = X0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_590,plain,
% 3.92/0.98      ( k1_xboole_0 = X0
% 3.92/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.92/0.98      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_19,negated_conjecture,
% 3.92/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.92/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_587,plain,
% 3.92/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_11,plain,
% 3.92/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.92/0.98      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 3.92/0.98      | k1_xboole_0 = X0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_595,plain,
% 3.92/0.98      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 3.92/0.98      | k1_xboole_0 = X1
% 3.92/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2593,plain,
% 3.92/0.98      ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3) | sK3 = k1_xboole_0 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_587,c_595]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_13,plain,
% 3.92/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.92/0.98      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 3.92/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_593,plain,
% 3.92/0.98      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 3.92/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_1991,plain,
% 3.92/0.98      ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_587,c_593]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2602,plain,
% 3.92/0.98      ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 3.92/0.98      inference(light_normalisation,[status(thm)],[c_2593,c_1991]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_20,negated_conjecture,
% 3.92/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.92/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_586,plain,
% 3.92/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2594,plain,
% 3.92/0.98      ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2) | sK2 = k1_xboole_0 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_586,c_595]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_1992,plain,
% 3.92/0.98      ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_586,c_593]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2597,plain,
% 3.92/0.98      ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 3.92/0.98      inference(light_normalisation,[status(thm)],[c_2594,c_1992]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_17,negated_conjecture,
% 3.92/0.98      ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
% 3.92/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_589,plain,
% 3.92/0.98      ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_3176,plain,
% 3.92/0.98      ( sK2 = k1_xboole_0
% 3.92/0.98      | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_2597,c_589]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_3257,plain,
% 3.92/0.98      ( sK2 = k1_xboole_0
% 3.92/0.98      | sK3 = k1_xboole_0
% 3.92/0.98      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_2602,c_3176]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_3779,plain,
% 3.92/0.98      ( sK2 = k1_xboole_0
% 3.92/0.98      | sK3 = k1_xboole_0
% 3.92/0.98      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_590,c_3257]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_18,negated_conjecture,
% 3.92/0.98      ( r1_tarski(sK2,sK3) ),
% 3.92/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_23,plain,
% 3.92/0.98      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_3782,plain,
% 3.92/0.98      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.92/0.98      inference(global_propositional_subsumption,
% 3.92/0.98                [status(thm)],
% 3.92/0.98                [c_3779,c_23]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_3783,plain,
% 3.92/0.98      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.92/0.98      inference(renaming,[status(thm)],[c_3782]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_3795,plain,
% 3.92/0.98      ( sK3 = k1_xboole_0
% 3.92/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_3783,c_586]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_22,plain,
% 3.92/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_8,plain,
% 3.92/0.98      ( k5_xboole_0(k1_tarski(X0),k1_setfam_1(k1_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0)))) != k1_tarski(X0) ),
% 3.92/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_47,plain,
% 3.92/0.98      ( k5_xboole_0(k1_tarski(k1_xboole_0),k1_setfam_1(k1_enumset1(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)))) != k1_tarski(k1_xboole_0) ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_7,plain,
% 3.92/0.98      ( X0 = X1
% 3.92/0.98      | k5_xboole_0(k1_tarski(X1),k1_setfam_1(k1_enumset1(k1_tarski(X1),k1_tarski(X1),k1_tarski(X0)))) = k1_tarski(X1) ),
% 3.92/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_48,plain,
% 3.92/0.98      ( k5_xboole_0(k1_tarski(k1_xboole_0),k1_setfam_1(k1_enumset1(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)))) = k1_tarski(k1_xboole_0)
% 3.92/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_201,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_884,plain,
% 3.92/0.98      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_201]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_885,plain,
% 3.92/0.98      ( sK3 != k1_xboole_0
% 3.92/0.98      | k1_xboole_0 = sK3
% 3.92/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_884]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_207,plain,
% 3.92/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.92/0.98      theory(equality) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_772,plain,
% 3.92/0.98      ( m1_subset_1(X0,X1)
% 3.92/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 3.92/0.98      | X1 != k1_zfmisc_1(k1_zfmisc_1(sK1))
% 3.92/0.98      | X0 != sK3 ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_207]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_1001,plain,
% 3.92/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 3.92/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 3.92/0.98      | X0 != sK3
% 3.92/0.98      | k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1)) ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_772]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_1003,plain,
% 3.92/0.98      ( X0 != sK3
% 3.92/0.98      | k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
% 3.92/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
% 3.92/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_1001]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_1005,plain,
% 3.92/0.98      ( k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
% 3.92/0.98      | k1_xboole_0 != sK3
% 3.92/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.92/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_1003]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_200,plain,( X0 = X0 ),theory(equality) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_1002,plain,
% 3.92/0.98      ( k1_zfmisc_1(k1_zfmisc_1(sK1)) = k1_zfmisc_1(k1_zfmisc_1(sK1)) ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_200]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_4173,plain,
% 3.92/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.92/0.98      inference(global_propositional_subsumption,
% 3.92/0.98                [status(thm)],
% 3.92/0.98                [c_3795,c_22,c_47,c_48,c_885,c_1005,c_1002]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_10,plain,
% 3.92/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 3.92/0.98      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_596,plain,
% 3.92/0.98      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 3.92/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_4179,plain,
% 3.92/0.98      ( k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_4173,c_596]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_3794,plain,
% 3.92/0.98      ( sK3 = k1_xboole_0
% 3.92/0.98      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_3783,c_589]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_4197,plain,
% 3.92/0.98      ( sK3 = k1_xboole_0
% 3.92/0.98      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
% 3.92/0.98      inference(demodulation,[status(thm)],[c_4179,c_3794]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_12,plain,
% 3.92/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.92/0.98      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.92/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_735,plain,
% 3.92/0.98      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
% 3.92/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_736,plain,
% 3.92/0.98      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 3.92/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_15,plain,
% 3.92/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.92/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_844,plain,
% 3.92/0.98      ( r1_tarski(k8_setfam_1(sK1,sK3),sK1)
% 3.92/0.98      | ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_845,plain,
% 3.92/0.98      ( r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top
% 3.92/0.98      | m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_844]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_5074,plain,
% 3.92/0.98      ( sK3 = k1_xboole_0 ),
% 3.92/0.98      inference(global_propositional_subsumption,
% 3.92/0.98                [status(thm)],
% 3.92/0.98                [c_4197,c_22,c_736,c_845]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_588,plain,
% 3.92/0.98      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_9,plain,
% 3.92/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.92/0.98      | ~ v1_xboole_0(X1)
% 3.92/0.98      | v1_xboole_0(X0) ),
% 3.92/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_14,plain,
% 3.92/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.92/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_123,plain,
% 3.92/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.92/0.98      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_153,plain,
% 3.92/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.92/0.98      inference(bin_hyper_res,[status(thm)],[c_9,c_123]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_585,plain,
% 3.92/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.92/0.98      | v1_xboole_0(X1) != iProver_top
% 3.92/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_153]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_1031,plain,
% 3.92/0.98      ( v1_xboole_0(sK2) = iProver_top
% 3.92/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_588,c_585]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_5085,plain,
% 3.92/0.98      ( v1_xboole_0(sK2) = iProver_top
% 3.92/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.92/0.98      inference(demodulation,[status(thm)],[c_5074,c_1031]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_5515,plain,
% 3.92/0.98      ( k5_xboole_0(k1_tarski(sK0(k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_tarski(sK0(k1_xboole_0)))))) = k1_xboole_0
% 3.92/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_2801,c_5085]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_3,plain,
% 3.92/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_598,plain,
% 3.92/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_7118,plain,
% 3.92/0.98      ( k5_xboole_0(k1_tarski(sK0(k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_tarski(sK0(k1_xboole_0)))))) = k1_xboole_0
% 3.92/0.98      | sK2 = k1_xboole_0 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_5515,c_598]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_4,plain,
% 3.92/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))) != k1_xboole_0
% 3.92/0.98      | k1_xboole_0 = X0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_7396,plain,
% 3.92/0.98      ( k1_tarski(sK0(k1_xboole_0)) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_7118,c_4]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2,plain,
% 3.92/0.98      ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_5,plain,
% 3.92/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_641,plain,
% 3.92/0.98      ( k1_tarski(X0) != k1_xboole_0 ),
% 3.92/0.98      inference(demodulation,[status(thm)],[c_8,c_2,c_5]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_7399,plain,
% 3.92/0.98      ( sK2 = k1_xboole_0 ),
% 3.92/0.98      inference(forward_subsumption_resolution,
% 3.92/0.98                [status(thm)],
% 3.92/0.98                [c_7396,c_641]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_5086,plain,
% 3.92/0.98      ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 3.92/0.98      inference(demodulation,[status(thm)],[c_5074,c_589]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_5092,plain,
% 3.92/0.98      ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
% 3.92/0.98      inference(light_normalisation,[status(thm)],[c_5086,c_4179]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_7407,plain,
% 3.92/0.98      ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 3.92/0.98      inference(demodulation,[status(thm)],[c_7399,c_5092]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_7419,plain,
% 3.92/0.98      ( r1_tarski(sK1,sK1) != iProver_top ),
% 3.92/0.98      inference(light_normalisation,[status(thm)],[c_7407,c_4179]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_594,plain,
% 3.92/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.92/0.98      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_591,plain,
% 3.92/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.92/0.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2186,plain,
% 3.92/0.98      ( r1_tarski(k8_setfam_1(X0,X1),X0) = iProver_top
% 3.92/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_594,c_591]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_4181,plain,
% 3.92/0.98      ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),sK1) = iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_4173,c_2186]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_4188,plain,
% 3.92/0.98      ( r1_tarski(sK1,sK1) = iProver_top ),
% 3.92/0.98      inference(demodulation,[status(thm)],[c_4179,c_4181]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(contradiction,plain,
% 3.92/0.98      ( $false ),
% 3.92/0.98      inference(minisat,[status(thm)],[c_7419,c_4188]) ).
% 3.92/0.98  
% 3.92/0.98  
% 3.92/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.92/0.98  
% 3.92/0.98  ------                               Statistics
% 3.92/0.98  
% 3.92/0.98  ------ Selected
% 3.92/0.98  
% 3.92/0.98  total_time:                             0.223
% 3.92/0.98  
%------------------------------------------------------------------------------
