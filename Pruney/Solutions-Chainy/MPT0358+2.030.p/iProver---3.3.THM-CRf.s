%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:53 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 529 expanded)
%              Number of clauses        :   61 (  76 expanded)
%              Number of leaves         :   31 ( 157 expanded)
%              Depth                    :   23
%              Number of atoms          :  315 ( 823 expanded)
%              Number of equality atoms :  153 ( 532 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f15,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f56,f88])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f72,f82])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f71,f83])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f70,f84])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f76,f86])).

fof(f93,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) ),
    inference(definition_unfolding,[],[f58,f89,f89,f87])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f94,plain,(
    ! [X2,X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f59,f87,f87,f87,f87])).

fof(f23,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f95,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f75,f90])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f78,f89])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK1) != sK2
        | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & ( k1_subset_1(sK1) = sK2
        | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( k1_subset_1(sK1) != sK2
      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & ( k1_subset_1(sK1) = sK2
      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f45,f46])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ) ),
    inference(definition_unfolding,[],[f57,f89])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,
    ( k1_subset_1(sK1) != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f25,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,
    ( k1_xboole_0 != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f81,f77])).

fof(f80,plain,
    ( k1_subset_1(sK1) = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f80,f77])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1339,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_358,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
    inference(theory_normalisation,[status(thm)],[c_9,c_16,c_0])).

cnf(c_10,plain,
    ( k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_713,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
    inference(demodulation,[status(thm)],[c_358,c_10])).

cnf(c_18,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_714,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
    inference(light_normalisation,[status(thm)],[c_713,c_18])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_17,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_715,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(demodulation,[status(thm)],[c_714,c_11,c_17])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_218,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_219,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)))) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_357,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))))) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(theory_normalisation,[status(thm)],[c_219,c_16,c_0])).

cnf(c_717,plain,
    ( k5_xboole_0(sK2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(demodulation,[status(thm)],[c_715,c_357])).

cnf(c_779,plain,
    ( k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k3_subset_1(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_717])).

cnf(c_1079,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),X0)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_779,c_16])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))
    | k1_xboole_0 = X0 ),
    inference(theory_normalisation,[status(thm)],[c_8,c_16,c_0])).

cnf(c_654,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_1227,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_654])).

cnf(c_1230,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1227,c_10])).

cnf(c_1231,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1230,c_11,c_17,c_18])).

cnf(c_1245,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1231])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_13,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_231,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | k1_xboole_0 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_14])).

cnf(c_232,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_231])).

cnf(c_36,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_48,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_234,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_232,c_36,c_13,c_48])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_234])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_1137,plain,
    ( ~ r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_363,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_804,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_953,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_954,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_365,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_901,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK2)
    | X2 != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_903,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_876,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_878,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_362,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_799,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_782,plain,
    ( r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),X0)
    | ~ r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),sK2)
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_784,plain,
    ( ~ r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),sK2)
    | r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),k1_xboole_0)
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_762,plain,
    ( r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),sK2)
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_40,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f98])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1339,c_1245,c_1137,c_954,c_903,c_878,c_799,c_784,c_762,c_48,c_40,c_13,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n006.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 17:55:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.45/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.02  
% 2.45/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/1.02  
% 2.45/1.02  ------  iProver source info
% 2.45/1.02  
% 2.45/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.45/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/1.02  git: non_committed_changes: false
% 2.45/1.02  git: last_make_outside_of_git: false
% 2.45/1.02  
% 2.45/1.02  ------ 
% 2.45/1.02  
% 2.45/1.02  ------ Input Options
% 2.45/1.02  
% 2.45/1.02  --out_options                           all
% 2.45/1.02  --tptp_safe_out                         true
% 2.45/1.02  --problem_path                          ""
% 2.45/1.02  --include_path                          ""
% 2.45/1.02  --clausifier                            res/vclausify_rel
% 2.45/1.02  --clausifier_options                    --mode clausify
% 2.45/1.02  --stdin                                 false
% 2.45/1.02  --stats_out                             all
% 2.45/1.02  
% 2.45/1.02  ------ General Options
% 2.45/1.02  
% 2.45/1.02  --fof                                   false
% 2.45/1.02  --time_out_real                         305.
% 2.45/1.02  --time_out_virtual                      -1.
% 2.45/1.02  --symbol_type_check                     false
% 2.45/1.02  --clausify_out                          false
% 2.45/1.02  --sig_cnt_out                           false
% 2.45/1.02  --trig_cnt_out                          false
% 2.45/1.02  --trig_cnt_out_tolerance                1.
% 2.45/1.02  --trig_cnt_out_sk_spl                   false
% 2.45/1.02  --abstr_cl_out                          false
% 2.45/1.02  
% 2.45/1.02  ------ Global Options
% 2.45/1.02  
% 2.45/1.02  --schedule                              default
% 2.45/1.02  --add_important_lit                     false
% 2.45/1.02  --prop_solver_per_cl                    1000
% 2.45/1.02  --min_unsat_core                        false
% 2.45/1.02  --soft_assumptions                      false
% 2.45/1.02  --soft_lemma_size                       3
% 2.45/1.02  --prop_impl_unit_size                   0
% 2.45/1.02  --prop_impl_unit                        []
% 2.45/1.02  --share_sel_clauses                     true
% 2.45/1.02  --reset_solvers                         false
% 2.45/1.02  --bc_imp_inh                            [conj_cone]
% 2.45/1.02  --conj_cone_tolerance                   3.
% 2.45/1.02  --extra_neg_conj                        none
% 2.45/1.02  --large_theory_mode                     true
% 2.45/1.02  --prolific_symb_bound                   200
% 2.45/1.02  --lt_threshold                          2000
% 2.45/1.02  --clause_weak_htbl                      true
% 2.45/1.02  --gc_record_bc_elim                     false
% 2.45/1.02  
% 2.45/1.02  ------ Preprocessing Options
% 2.45/1.02  
% 2.45/1.02  --preprocessing_flag                    true
% 2.45/1.02  --time_out_prep_mult                    0.1
% 2.45/1.02  --splitting_mode                        input
% 2.45/1.02  --splitting_grd                         true
% 2.45/1.02  --splitting_cvd                         false
% 2.45/1.02  --splitting_cvd_svl                     false
% 2.45/1.02  --splitting_nvd                         32
% 2.45/1.02  --sub_typing                            true
% 2.45/1.02  --prep_gs_sim                           true
% 2.45/1.02  --prep_unflatten                        true
% 2.45/1.02  --prep_res_sim                          true
% 2.45/1.02  --prep_upred                            true
% 2.45/1.02  --prep_sem_filter                       exhaustive
% 2.45/1.02  --prep_sem_filter_out                   false
% 2.45/1.02  --pred_elim                             true
% 2.45/1.02  --res_sim_input                         true
% 2.45/1.02  --eq_ax_congr_red                       true
% 2.45/1.02  --pure_diseq_elim                       true
% 2.45/1.02  --brand_transform                       false
% 2.45/1.02  --non_eq_to_eq                          false
% 2.45/1.02  --prep_def_merge                        true
% 2.45/1.02  --prep_def_merge_prop_impl              false
% 2.45/1.02  --prep_def_merge_mbd                    true
% 2.45/1.02  --prep_def_merge_tr_red                 false
% 2.45/1.02  --prep_def_merge_tr_cl                  false
% 2.45/1.02  --smt_preprocessing                     true
% 2.45/1.02  --smt_ac_axioms                         fast
% 2.45/1.02  --preprocessed_out                      false
% 2.45/1.02  --preprocessed_stats                    false
% 2.45/1.02  
% 2.45/1.02  ------ Abstraction refinement Options
% 2.45/1.02  
% 2.45/1.02  --abstr_ref                             []
% 2.45/1.02  --abstr_ref_prep                        false
% 2.45/1.02  --abstr_ref_until_sat                   false
% 2.45/1.02  --abstr_ref_sig_restrict                funpre
% 2.45/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.02  --abstr_ref_under                       []
% 2.45/1.02  
% 2.45/1.02  ------ SAT Options
% 2.45/1.02  
% 2.45/1.02  --sat_mode                              false
% 2.45/1.02  --sat_fm_restart_options                ""
% 2.45/1.02  --sat_gr_def                            false
% 2.45/1.02  --sat_epr_types                         true
% 2.45/1.02  --sat_non_cyclic_types                  false
% 2.45/1.02  --sat_finite_models                     false
% 2.45/1.02  --sat_fm_lemmas                         false
% 2.45/1.02  --sat_fm_prep                           false
% 2.45/1.02  --sat_fm_uc_incr                        true
% 2.45/1.02  --sat_out_model                         small
% 2.45/1.02  --sat_out_clauses                       false
% 2.45/1.02  
% 2.45/1.02  ------ QBF Options
% 2.45/1.02  
% 2.45/1.02  --qbf_mode                              false
% 2.45/1.02  --qbf_elim_univ                         false
% 2.45/1.02  --qbf_dom_inst                          none
% 2.45/1.02  --qbf_dom_pre_inst                      false
% 2.45/1.02  --qbf_sk_in                             false
% 2.45/1.02  --qbf_pred_elim                         true
% 2.45/1.02  --qbf_split                             512
% 2.45/1.02  
% 2.45/1.02  ------ BMC1 Options
% 2.45/1.02  
% 2.45/1.02  --bmc1_incremental                      false
% 2.45/1.02  --bmc1_axioms                           reachable_all
% 2.45/1.02  --bmc1_min_bound                        0
% 2.45/1.02  --bmc1_max_bound                        -1
% 2.45/1.02  --bmc1_max_bound_default                -1
% 2.45/1.02  --bmc1_symbol_reachability              true
% 2.45/1.02  --bmc1_property_lemmas                  false
% 2.45/1.02  --bmc1_k_induction                      false
% 2.45/1.02  --bmc1_non_equiv_states                 false
% 2.45/1.02  --bmc1_deadlock                         false
% 2.45/1.02  --bmc1_ucm                              false
% 2.45/1.02  --bmc1_add_unsat_core                   none
% 2.45/1.02  --bmc1_unsat_core_children              false
% 2.45/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.02  --bmc1_out_stat                         full
% 2.45/1.02  --bmc1_ground_init                      false
% 2.45/1.02  --bmc1_pre_inst_next_state              false
% 2.45/1.02  --bmc1_pre_inst_state                   false
% 2.45/1.02  --bmc1_pre_inst_reach_state             false
% 2.45/1.02  --bmc1_out_unsat_core                   false
% 2.45/1.02  --bmc1_aig_witness_out                  false
% 2.45/1.02  --bmc1_verbose                          false
% 2.45/1.02  --bmc1_dump_clauses_tptp                false
% 2.45/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.02  --bmc1_dump_file                        -
% 2.45/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.02  --bmc1_ucm_extend_mode                  1
% 2.45/1.02  --bmc1_ucm_init_mode                    2
% 2.45/1.02  --bmc1_ucm_cone_mode                    none
% 2.45/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.02  --bmc1_ucm_relax_model                  4
% 2.45/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.02  --bmc1_ucm_layered_model                none
% 2.45/1.02  --bmc1_ucm_max_lemma_size               10
% 2.45/1.02  
% 2.45/1.02  ------ AIG Options
% 2.45/1.02  
% 2.45/1.02  --aig_mode                              false
% 2.45/1.02  
% 2.45/1.02  ------ Instantiation Options
% 2.45/1.02  
% 2.45/1.02  --instantiation_flag                    true
% 2.45/1.02  --inst_sos_flag                         false
% 2.45/1.02  --inst_sos_phase                        true
% 2.45/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.02  --inst_lit_sel_side                     num_symb
% 2.45/1.02  --inst_solver_per_active                1400
% 2.45/1.02  --inst_solver_calls_frac                1.
% 2.45/1.02  --inst_passive_queue_type               priority_queues
% 2.45/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.02  --inst_passive_queues_freq              [25;2]
% 2.45/1.02  --inst_dismatching                      true
% 2.45/1.02  --inst_eager_unprocessed_to_passive     true
% 2.45/1.02  --inst_prop_sim_given                   true
% 2.45/1.02  --inst_prop_sim_new                     false
% 2.45/1.02  --inst_subs_new                         false
% 2.45/1.02  --inst_eq_res_simp                      false
% 2.45/1.02  --inst_subs_given                       false
% 2.45/1.02  --inst_orphan_elimination               true
% 2.45/1.02  --inst_learning_loop_flag               true
% 2.45/1.02  --inst_learning_start                   3000
% 2.45/1.02  --inst_learning_factor                  2
% 2.45/1.02  --inst_start_prop_sim_after_learn       3
% 2.45/1.02  --inst_sel_renew                        solver
% 2.45/1.02  --inst_lit_activity_flag                true
% 2.45/1.02  --inst_restr_to_given                   false
% 2.45/1.02  --inst_activity_threshold               500
% 2.45/1.02  --inst_out_proof                        true
% 2.45/1.02  
% 2.45/1.02  ------ Resolution Options
% 2.45/1.02  
% 2.45/1.02  --resolution_flag                       true
% 2.45/1.02  --res_lit_sel                           adaptive
% 2.45/1.02  --res_lit_sel_side                      none
% 2.45/1.02  --res_ordering                          kbo
% 2.45/1.02  --res_to_prop_solver                    active
% 2.45/1.02  --res_prop_simpl_new                    false
% 2.45/1.02  --res_prop_simpl_given                  true
% 2.45/1.02  --res_passive_queue_type                priority_queues
% 2.45/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.02  --res_passive_queues_freq               [15;5]
% 2.45/1.02  --res_forward_subs                      full
% 2.45/1.02  --res_backward_subs                     full
% 2.45/1.02  --res_forward_subs_resolution           true
% 2.45/1.02  --res_backward_subs_resolution          true
% 2.45/1.02  --res_orphan_elimination                true
% 2.45/1.02  --res_time_limit                        2.
% 2.45/1.02  --res_out_proof                         true
% 2.45/1.02  
% 2.45/1.02  ------ Superposition Options
% 2.45/1.02  
% 2.45/1.02  --superposition_flag                    true
% 2.45/1.02  --sup_passive_queue_type                priority_queues
% 2.45/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.02  --demod_completeness_check              fast
% 2.45/1.02  --demod_use_ground                      true
% 2.45/1.02  --sup_to_prop_solver                    passive
% 2.45/1.02  --sup_prop_simpl_new                    true
% 2.45/1.02  --sup_prop_simpl_given                  true
% 2.45/1.02  --sup_fun_splitting                     false
% 2.45/1.02  --sup_smt_interval                      50000
% 2.45/1.02  
% 2.45/1.02  ------ Superposition Simplification Setup
% 2.45/1.02  
% 2.45/1.02  --sup_indices_passive                   []
% 2.45/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.02  --sup_full_bw                           [BwDemod]
% 2.45/1.02  --sup_immed_triv                        [TrivRules]
% 2.45/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.02  --sup_immed_bw_main                     []
% 2.45/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.02  
% 2.45/1.02  ------ Combination Options
% 2.45/1.02  
% 2.45/1.02  --comb_res_mult                         3
% 2.45/1.02  --comb_sup_mult                         2
% 2.45/1.02  --comb_inst_mult                        10
% 2.45/1.02  
% 2.45/1.02  ------ Debug Options
% 2.45/1.02  
% 2.45/1.02  --dbg_backtrace                         false
% 2.45/1.02  --dbg_dump_prop_clauses                 false
% 2.45/1.02  --dbg_dump_prop_clauses_file            -
% 2.45/1.02  --dbg_out_stat                          false
% 2.45/1.02  ------ Parsing...
% 2.45/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/1.02  
% 2.45/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.45/1.02  
% 2.45/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/1.02  
% 2.45/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/1.02  ------ Proving...
% 2.45/1.02  ------ Problem Properties 
% 2.45/1.02  
% 2.45/1.02  
% 2.45/1.02  clauses                                 18
% 2.45/1.02  conjectures                             2
% 2.45/1.02  EPR                                     4
% 2.45/1.02  Horn                                    16
% 2.45/1.02  unary                                   10
% 2.45/1.02  binary                                  6
% 2.45/1.02  lits                                    28
% 2.45/1.02  lits eq                                 14
% 2.45/1.02  fd_pure                                 0
% 2.45/1.02  fd_pseudo                               0
% 2.45/1.02  fd_cond                                 1
% 2.45/1.02  fd_pseudo_cond                          1
% 2.45/1.02  AC symbols                              1
% 2.45/1.02  
% 2.45/1.02  ------ Schedule dynamic 5 is on 
% 2.45/1.02  
% 2.45/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/1.02  
% 2.45/1.02  
% 2.45/1.02  ------ 
% 2.45/1.02  Current options:
% 2.45/1.02  ------ 
% 2.45/1.02  
% 2.45/1.02  ------ Input Options
% 2.45/1.02  
% 2.45/1.02  --out_options                           all
% 2.45/1.02  --tptp_safe_out                         true
% 2.45/1.02  --problem_path                          ""
% 2.45/1.02  --include_path                          ""
% 2.45/1.02  --clausifier                            res/vclausify_rel
% 2.45/1.02  --clausifier_options                    --mode clausify
% 2.45/1.02  --stdin                                 false
% 2.45/1.02  --stats_out                             all
% 2.45/1.02  
% 2.45/1.02  ------ General Options
% 2.45/1.02  
% 2.45/1.02  --fof                                   false
% 2.45/1.02  --time_out_real                         305.
% 2.45/1.02  --time_out_virtual                      -1.
% 2.45/1.02  --symbol_type_check                     false
% 2.45/1.02  --clausify_out                          false
% 2.45/1.02  --sig_cnt_out                           false
% 2.45/1.02  --trig_cnt_out                          false
% 2.45/1.02  --trig_cnt_out_tolerance                1.
% 2.45/1.02  --trig_cnt_out_sk_spl                   false
% 2.45/1.02  --abstr_cl_out                          false
% 2.45/1.02  
% 2.45/1.02  ------ Global Options
% 2.45/1.02  
% 2.45/1.02  --schedule                              default
% 2.45/1.02  --add_important_lit                     false
% 2.45/1.02  --prop_solver_per_cl                    1000
% 2.45/1.02  --min_unsat_core                        false
% 2.45/1.02  --soft_assumptions                      false
% 2.45/1.02  --soft_lemma_size                       3
% 2.45/1.02  --prop_impl_unit_size                   0
% 2.45/1.02  --prop_impl_unit                        []
% 2.45/1.02  --share_sel_clauses                     true
% 2.45/1.02  --reset_solvers                         false
% 2.45/1.02  --bc_imp_inh                            [conj_cone]
% 2.45/1.02  --conj_cone_tolerance                   3.
% 2.45/1.02  --extra_neg_conj                        none
% 2.45/1.02  --large_theory_mode                     true
% 2.45/1.02  --prolific_symb_bound                   200
% 2.45/1.02  --lt_threshold                          2000
% 2.45/1.02  --clause_weak_htbl                      true
% 2.45/1.02  --gc_record_bc_elim                     false
% 2.45/1.02  
% 2.45/1.02  ------ Preprocessing Options
% 2.45/1.02  
% 2.45/1.02  --preprocessing_flag                    true
% 2.45/1.02  --time_out_prep_mult                    0.1
% 2.45/1.02  --splitting_mode                        input
% 2.45/1.02  --splitting_grd                         true
% 2.45/1.02  --splitting_cvd                         false
% 2.45/1.02  --splitting_cvd_svl                     false
% 2.45/1.02  --splitting_nvd                         32
% 2.45/1.02  --sub_typing                            true
% 2.45/1.02  --prep_gs_sim                           true
% 2.45/1.02  --prep_unflatten                        true
% 2.45/1.02  --prep_res_sim                          true
% 2.45/1.02  --prep_upred                            true
% 2.45/1.02  --prep_sem_filter                       exhaustive
% 2.45/1.02  --prep_sem_filter_out                   false
% 2.45/1.02  --pred_elim                             true
% 2.45/1.02  --res_sim_input                         true
% 2.45/1.02  --eq_ax_congr_red                       true
% 2.45/1.02  --pure_diseq_elim                       true
% 2.45/1.02  --brand_transform                       false
% 2.45/1.02  --non_eq_to_eq                          false
% 2.45/1.02  --prep_def_merge                        true
% 2.45/1.02  --prep_def_merge_prop_impl              false
% 2.45/1.02  --prep_def_merge_mbd                    true
% 2.45/1.02  --prep_def_merge_tr_red                 false
% 2.45/1.02  --prep_def_merge_tr_cl                  false
% 2.45/1.02  --smt_preprocessing                     true
% 2.45/1.02  --smt_ac_axioms                         fast
% 2.45/1.02  --preprocessed_out                      false
% 2.45/1.02  --preprocessed_stats                    false
% 2.45/1.02  
% 2.45/1.02  ------ Abstraction refinement Options
% 2.45/1.02  
% 2.45/1.02  --abstr_ref                             []
% 2.45/1.02  --abstr_ref_prep                        false
% 2.45/1.02  --abstr_ref_until_sat                   false
% 2.45/1.02  --abstr_ref_sig_restrict                funpre
% 2.45/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.02  --abstr_ref_under                       []
% 2.45/1.02  
% 2.45/1.02  ------ SAT Options
% 2.45/1.02  
% 2.45/1.02  --sat_mode                              false
% 2.45/1.02  --sat_fm_restart_options                ""
% 2.45/1.02  --sat_gr_def                            false
% 2.45/1.02  --sat_epr_types                         true
% 2.45/1.02  --sat_non_cyclic_types                  false
% 2.45/1.02  --sat_finite_models                     false
% 2.45/1.02  --sat_fm_lemmas                         false
% 2.45/1.02  --sat_fm_prep                           false
% 2.45/1.02  --sat_fm_uc_incr                        true
% 2.45/1.02  --sat_out_model                         small
% 2.45/1.02  --sat_out_clauses                       false
% 2.45/1.02  
% 2.45/1.02  ------ QBF Options
% 2.45/1.02  
% 2.45/1.02  --qbf_mode                              false
% 2.45/1.02  --qbf_elim_univ                         false
% 2.45/1.02  --qbf_dom_inst                          none
% 2.45/1.02  --qbf_dom_pre_inst                      false
% 2.45/1.02  --qbf_sk_in                             false
% 2.45/1.02  --qbf_pred_elim                         true
% 2.45/1.02  --qbf_split                             512
% 2.45/1.02  
% 2.45/1.02  ------ BMC1 Options
% 2.45/1.02  
% 2.45/1.02  --bmc1_incremental                      false
% 2.45/1.02  --bmc1_axioms                           reachable_all
% 2.45/1.02  --bmc1_min_bound                        0
% 2.45/1.02  --bmc1_max_bound                        -1
% 2.45/1.02  --bmc1_max_bound_default                -1
% 2.45/1.02  --bmc1_symbol_reachability              true
% 2.45/1.02  --bmc1_property_lemmas                  false
% 2.45/1.02  --bmc1_k_induction                      false
% 2.45/1.02  --bmc1_non_equiv_states                 false
% 2.45/1.02  --bmc1_deadlock                         false
% 2.45/1.02  --bmc1_ucm                              false
% 2.45/1.02  --bmc1_add_unsat_core                   none
% 2.45/1.02  --bmc1_unsat_core_children              false
% 2.45/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.02  --bmc1_out_stat                         full
% 2.45/1.02  --bmc1_ground_init                      false
% 2.45/1.02  --bmc1_pre_inst_next_state              false
% 2.45/1.02  --bmc1_pre_inst_state                   false
% 2.45/1.02  --bmc1_pre_inst_reach_state             false
% 2.45/1.02  --bmc1_out_unsat_core                   false
% 2.45/1.02  --bmc1_aig_witness_out                  false
% 2.45/1.02  --bmc1_verbose                          false
% 2.45/1.02  --bmc1_dump_clauses_tptp                false
% 2.45/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.02  --bmc1_dump_file                        -
% 2.45/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.02  --bmc1_ucm_extend_mode                  1
% 2.45/1.02  --bmc1_ucm_init_mode                    2
% 2.45/1.02  --bmc1_ucm_cone_mode                    none
% 2.45/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.02  --bmc1_ucm_relax_model                  4
% 2.45/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.02  --bmc1_ucm_layered_model                none
% 2.45/1.02  --bmc1_ucm_max_lemma_size               10
% 2.45/1.02  
% 2.45/1.02  ------ AIG Options
% 2.45/1.02  
% 2.45/1.02  --aig_mode                              false
% 2.45/1.02  
% 2.45/1.02  ------ Instantiation Options
% 2.45/1.02  
% 2.45/1.02  --instantiation_flag                    true
% 2.45/1.02  --inst_sos_flag                         false
% 2.45/1.02  --inst_sos_phase                        true
% 2.45/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.02  --inst_lit_sel_side                     none
% 2.45/1.02  --inst_solver_per_active                1400
% 2.45/1.02  --inst_solver_calls_frac                1.
% 2.45/1.02  --inst_passive_queue_type               priority_queues
% 2.45/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.02  --inst_passive_queues_freq              [25;2]
% 2.45/1.02  --inst_dismatching                      true
% 2.45/1.02  --inst_eager_unprocessed_to_passive     true
% 2.45/1.02  --inst_prop_sim_given                   true
% 2.45/1.02  --inst_prop_sim_new                     false
% 2.45/1.02  --inst_subs_new                         false
% 2.45/1.02  --inst_eq_res_simp                      false
% 2.45/1.02  --inst_subs_given                       false
% 2.45/1.02  --inst_orphan_elimination               true
% 2.45/1.02  --inst_learning_loop_flag               true
% 2.45/1.02  --inst_learning_start                   3000
% 2.45/1.02  --inst_learning_factor                  2
% 2.45/1.02  --inst_start_prop_sim_after_learn       3
% 2.45/1.02  --inst_sel_renew                        solver
% 2.45/1.02  --inst_lit_activity_flag                true
% 2.45/1.02  --inst_restr_to_given                   false
% 2.45/1.02  --inst_activity_threshold               500
% 2.45/1.02  --inst_out_proof                        true
% 2.45/1.02  
% 2.45/1.02  ------ Resolution Options
% 2.45/1.02  
% 2.45/1.02  --resolution_flag                       false
% 2.45/1.02  --res_lit_sel                           adaptive
% 2.45/1.02  --res_lit_sel_side                      none
% 2.45/1.02  --res_ordering                          kbo
% 2.45/1.02  --res_to_prop_solver                    active
% 2.45/1.02  --res_prop_simpl_new                    false
% 2.45/1.02  --res_prop_simpl_given                  true
% 2.45/1.02  --res_passive_queue_type                priority_queues
% 2.45/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.02  --res_passive_queues_freq               [15;5]
% 2.45/1.02  --res_forward_subs                      full
% 2.45/1.02  --res_backward_subs                     full
% 2.45/1.02  --res_forward_subs_resolution           true
% 2.45/1.02  --res_backward_subs_resolution          true
% 2.45/1.02  --res_orphan_elimination                true
% 2.45/1.02  --res_time_limit                        2.
% 2.45/1.02  --res_out_proof                         true
% 2.45/1.02  
% 2.45/1.02  ------ Superposition Options
% 2.45/1.02  
% 2.45/1.02  --superposition_flag                    true
% 2.45/1.02  --sup_passive_queue_type                priority_queues
% 2.45/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.02  --demod_completeness_check              fast
% 2.45/1.02  --demod_use_ground                      true
% 2.45/1.02  --sup_to_prop_solver                    passive
% 2.45/1.02  --sup_prop_simpl_new                    true
% 2.45/1.02  --sup_prop_simpl_given                  true
% 2.45/1.02  --sup_fun_splitting                     false
% 2.45/1.02  --sup_smt_interval                      50000
% 2.45/1.02  
% 2.45/1.02  ------ Superposition Simplification Setup
% 2.45/1.02  
% 2.45/1.02  --sup_indices_passive                   []
% 2.45/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.02  --sup_full_bw                           [BwDemod]
% 2.45/1.02  --sup_immed_triv                        [TrivRules]
% 2.45/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.02  --sup_immed_bw_main                     []
% 2.45/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.02  
% 2.45/1.02  ------ Combination Options
% 2.45/1.02  
% 2.45/1.02  --comb_res_mult                         3
% 2.45/1.02  --comb_sup_mult                         2
% 2.45/1.02  --comb_inst_mult                        10
% 2.45/1.02  
% 2.45/1.02  ------ Debug Options
% 2.45/1.02  
% 2.45/1.02  --dbg_backtrace                         false
% 2.45/1.02  --dbg_dump_prop_clauses                 false
% 2.45/1.02  --dbg_dump_prop_clauses_file            -
% 2.45/1.02  --dbg_out_stat                          false
% 2.45/1.02  
% 2.45/1.02  
% 2.45/1.02  
% 2.45/1.02  
% 2.45/1.02  ------ Proving...
% 2.45/1.02  
% 2.45/1.02  
% 2.45/1.02  % SZS status Theorem for theBenchmark.p
% 2.45/1.02  
% 2.45/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/1.02  
% 2.45/1.02  fof(f4,axiom,(
% 2.45/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f42,plain,(
% 2.45/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.45/1.02    inference(nnf_transformation,[],[f4])).
% 2.45/1.02  
% 2.45/1.02  fof(f43,plain,(
% 2.45/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.45/1.02    inference(flattening,[],[f42])).
% 2.45/1.02  
% 2.45/1.02  fof(f55,plain,(
% 2.45/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f43])).
% 2.45/1.02  
% 2.45/1.02  fof(f7,axiom,(
% 2.45/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f58,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f7])).
% 2.45/1.02  
% 2.45/1.02  fof(f5,axiom,(
% 2.45/1.02    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f56,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f5])).
% 2.45/1.02  
% 2.45/1.02  fof(f15,axiom,(
% 2.45/1.02    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f67,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f15])).
% 2.45/1.02  
% 2.45/1.02  fof(f88,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 2.45/1.02    inference(definition_unfolding,[],[f67,f87])).
% 2.45/1.02  
% 2.45/1.02  fof(f89,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 2.45/1.02    inference(definition_unfolding,[],[f56,f88])).
% 2.45/1.02  
% 2.45/1.02  fof(f24,axiom,(
% 2.45/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f76,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.45/1.02    inference(cnf_transformation,[],[f24])).
% 2.45/1.02  
% 2.45/1.02  fof(f17,axiom,(
% 2.45/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f69,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f17])).
% 2.45/1.02  
% 2.45/1.02  fof(f18,axiom,(
% 2.45/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f70,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f18])).
% 2.45/1.02  
% 2.45/1.02  fof(f19,axiom,(
% 2.45/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f71,plain,(
% 2.45/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f19])).
% 2.45/1.02  
% 2.45/1.02  fof(f20,axiom,(
% 2.45/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f72,plain,(
% 2.45/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f20])).
% 2.45/1.02  
% 2.45/1.02  fof(f21,axiom,(
% 2.45/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f73,plain,(
% 2.45/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f21])).
% 2.45/1.02  
% 2.45/1.02  fof(f22,axiom,(
% 2.45/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f74,plain,(
% 2.45/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f22])).
% 2.45/1.02  
% 2.45/1.02  fof(f82,plain,(
% 2.45/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.45/1.02    inference(definition_unfolding,[],[f73,f74])).
% 2.45/1.02  
% 2.45/1.02  fof(f83,plain,(
% 2.45/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.45/1.02    inference(definition_unfolding,[],[f72,f82])).
% 2.45/1.02  
% 2.45/1.02  fof(f84,plain,(
% 2.45/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.45/1.02    inference(definition_unfolding,[],[f71,f83])).
% 2.45/1.02  
% 2.45/1.02  fof(f85,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.45/1.02    inference(definition_unfolding,[],[f70,f84])).
% 2.45/1.02  
% 2.45/1.02  fof(f86,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.45/1.02    inference(definition_unfolding,[],[f69,f85])).
% 2.45/1.02  
% 2.45/1.02  fof(f87,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.45/1.02    inference(definition_unfolding,[],[f76,f86])).
% 2.45/1.02  
% 2.45/1.02  fof(f93,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1))))) )),
% 2.45/1.02    inference(definition_unfolding,[],[f58,f89,f89,f87])).
% 2.45/1.02  
% 2.45/1.02  fof(f13,axiom,(
% 2.45/1.02    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f65,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f13])).
% 2.45/1.02  
% 2.45/1.02  fof(f1,axiom,(
% 2.45/1.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f48,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f1])).
% 2.45/1.02  
% 2.45/1.02  fof(f8,axiom,(
% 2.45/1.02    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f59,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f8])).
% 2.45/1.02  
% 2.45/1.02  fof(f94,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) )),
% 2.45/1.02    inference(definition_unfolding,[],[f59,f87,f87,f87,f87])).
% 2.45/1.02  
% 2.45/1.02  fof(f23,axiom,(
% 2.45/1.02    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f75,plain,(
% 2.45/1.02    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 2.45/1.02    inference(cnf_transformation,[],[f23])).
% 2.45/1.02  
% 2.45/1.02  fof(f16,axiom,(
% 2.45/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f68,plain,(
% 2.45/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f16])).
% 2.45/1.02  
% 2.45/1.02  fof(f90,plain,(
% 2.45/1.02    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.45/1.02    inference(definition_unfolding,[],[f68,f86])).
% 2.45/1.02  
% 2.45/1.02  fof(f95,plain,(
% 2.45/1.02    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.45/1.02    inference(definition_unfolding,[],[f75,f90])).
% 2.45/1.02  
% 2.45/1.02  fof(f9,axiom,(
% 2.45/1.02    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f60,plain,(
% 2.45/1.02    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.45/1.02    inference(cnf_transformation,[],[f9])).
% 2.45/1.02  
% 2.45/1.02  fof(f14,axiom,(
% 2.45/1.02    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f66,plain,(
% 2.45/1.02    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 2.45/1.02    inference(cnf_transformation,[],[f14])).
% 2.45/1.02  
% 2.45/1.02  fof(f26,axiom,(
% 2.45/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f36,plain,(
% 2.45/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/1.02    inference(ennf_transformation,[],[f26])).
% 2.45/1.02  
% 2.45/1.02  fof(f78,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.45/1.02    inference(cnf_transformation,[],[f36])).
% 2.45/1.02  
% 2.45/1.02  fof(f96,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.45/1.02    inference(definition_unfolding,[],[f78,f89])).
% 2.45/1.02  
% 2.45/1.02  fof(f27,conjecture,(
% 2.45/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f28,negated_conjecture,(
% 2.45/1.02    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.45/1.02    inference(negated_conjecture,[],[f27])).
% 2.45/1.02  
% 2.45/1.02  fof(f37,plain,(
% 2.45/1.02    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/1.02    inference(ennf_transformation,[],[f28])).
% 2.45/1.02  
% 2.45/1.02  fof(f44,plain,(
% 2.45/1.02    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/1.02    inference(nnf_transformation,[],[f37])).
% 2.45/1.02  
% 2.45/1.02  fof(f45,plain,(
% 2.45/1.02    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/1.02    inference(flattening,[],[f44])).
% 2.45/1.02  
% 2.45/1.02  fof(f46,plain,(
% 2.45/1.02    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 2.45/1.02    introduced(choice_axiom,[])).
% 2.45/1.02  
% 2.45/1.02  fof(f47,plain,(
% 2.45/1.02    (k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.45/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f45,f46])).
% 2.45/1.02  
% 2.45/1.02  fof(f79,plain,(
% 2.45/1.02    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.45/1.02    inference(cnf_transformation,[],[f47])).
% 2.45/1.02  
% 2.45/1.02  fof(f6,axiom,(
% 2.45/1.02    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f31,plain,(
% 2.45/1.02    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 2.45/1.02    inference(ennf_transformation,[],[f6])).
% 2.45/1.02  
% 2.45/1.02  fof(f57,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 2.45/1.02    inference(cnf_transformation,[],[f31])).
% 2.45/1.02  
% 2.45/1.02  fof(f92,plain,(
% 2.45/1.02    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) )),
% 2.45/1.02    inference(definition_unfolding,[],[f57,f89])).
% 2.45/1.02  
% 2.45/1.02  fof(f12,axiom,(
% 2.45/1.02    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f35,plain,(
% 2.45/1.02    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 2.45/1.02    inference(ennf_transformation,[],[f12])).
% 2.45/1.02  
% 2.45/1.02  fof(f64,plain,(
% 2.45/1.02    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f35])).
% 2.45/1.02  
% 2.45/1.02  fof(f10,axiom,(
% 2.45/1.02    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f32,plain,(
% 2.45/1.02    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.45/1.02    inference(ennf_transformation,[],[f10])).
% 2.45/1.02  
% 2.45/1.02  fof(f61,plain,(
% 2.45/1.02    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f32])).
% 2.45/1.02  
% 2.45/1.02  fof(f101,plain,(
% 2.45/1.02    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.45/1.02    inference(equality_resolution,[],[f61])).
% 2.45/1.02  
% 2.45/1.02  fof(f11,axiom,(
% 2.45/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f33,plain,(
% 2.45/1.02    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.45/1.02    inference(ennf_transformation,[],[f11])).
% 2.45/1.02  
% 2.45/1.02  fof(f34,plain,(
% 2.45/1.02    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.45/1.02    inference(flattening,[],[f33])).
% 2.45/1.02  
% 2.45/1.02  fof(f63,plain,(
% 2.45/1.02    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f34])).
% 2.45/1.02  
% 2.45/1.02  fof(f53,plain,(
% 2.45/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.45/1.02    inference(cnf_transformation,[],[f43])).
% 2.45/1.02  
% 2.45/1.02  fof(f100,plain,(
% 2.45/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.45/1.02    inference(equality_resolution,[],[f53])).
% 2.45/1.02  
% 2.45/1.02  fof(f2,axiom,(
% 2.45/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f30,plain,(
% 2.45/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.45/1.02    inference(ennf_transformation,[],[f2])).
% 2.45/1.02  
% 2.45/1.02  fof(f38,plain,(
% 2.45/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/1.02    inference(nnf_transformation,[],[f30])).
% 2.45/1.02  
% 2.45/1.02  fof(f39,plain,(
% 2.45/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/1.02    inference(rectify,[],[f38])).
% 2.45/1.02  
% 2.45/1.02  fof(f40,plain,(
% 2.45/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.45/1.02    introduced(choice_axiom,[])).
% 2.45/1.02  
% 2.45/1.02  fof(f41,plain,(
% 2.45/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.45/1.02  
% 2.45/1.02  fof(f49,plain,(
% 2.45/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f41])).
% 2.45/1.02  
% 2.45/1.02  fof(f50,plain,(
% 2.45/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f41])).
% 2.45/1.02  
% 2.45/1.02  fof(f62,plain,(
% 2.45/1.02    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.45/1.02    inference(cnf_transformation,[],[f32])).
% 2.45/1.02  
% 2.45/1.02  fof(f81,plain,(
% 2.45/1.02    k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.45/1.02    inference(cnf_transformation,[],[f47])).
% 2.45/1.02  
% 2.45/1.02  fof(f25,axiom,(
% 2.45/1.02    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f77,plain,(
% 2.45/1.02    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f25])).
% 2.45/1.02  
% 2.45/1.02  fof(f97,plain,(
% 2.45/1.02    k1_xboole_0 != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.45/1.02    inference(definition_unfolding,[],[f81,f77])).
% 2.45/1.02  
% 2.45/1.02  fof(f80,plain,(
% 2.45/1.02    k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.45/1.02    inference(cnf_transformation,[],[f47])).
% 2.45/1.02  
% 2.45/1.02  fof(f98,plain,(
% 2.45/1.02    k1_xboole_0 = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.45/1.02    inference(definition_unfolding,[],[f80,f77])).
% 2.45/1.02  
% 2.45/1.02  cnf(c_5,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.45/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1339,plain,
% 2.45/1.02      ( ~ r1_tarski(sK2,k1_xboole_0)
% 2.45/1.02      | ~ r1_tarski(k1_xboole_0,sK2)
% 2.45/1.02      | k1_xboole_0 = sK2 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_9,plain,
% 2.45/1.02      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
% 2.45/1.02      inference(cnf_transformation,[],[f93]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_16,plain,
% 2.45/1.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.45/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_0,plain,
% 2.45/1.02      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_358,plain,
% 2.45/1.02      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
% 2.45/1.02      inference(theory_normalisation,[status(thm)],[c_9,c_16,c_0]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_10,plain,
% 2.45/1.02      ( k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 2.45/1.02      inference(cnf_transformation,[],[f94]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_713,plain,
% 2.45/1.02      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
% 2.45/1.02      inference(demodulation,[status(thm)],[c_358,c_10]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_18,plain,
% 2.45/1.02      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 2.45/1.02      inference(cnf_transformation,[],[f95]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_714,plain,
% 2.45/1.02      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
% 2.45/1.02      inference(light_normalisation,[status(thm)],[c_713,c_18]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_11,plain,
% 2.45/1.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.45/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_17,plain,
% 2.45/1.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.45/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_715,plain,
% 2.45/1.02      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 2.45/1.02      inference(demodulation,[status(thm)],[c_714,c_11,c_17]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_19,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.45/1.02      | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k3_subset_1(X1,X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f96]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_22,negated_conjecture,
% 2.45/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 2.45/1.02      inference(cnf_transformation,[],[f79]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_218,plain,
% 2.45/1.02      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k3_subset_1(X0,X1)
% 2.45/1.02      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 2.45/1.02      | sK2 != X1 ),
% 2.45/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_219,plain,
% 2.45/1.02      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)))) = k3_subset_1(X0,sK2)
% 2.45/1.02      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 2.45/1.02      inference(unflattening,[status(thm)],[c_218]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_357,plain,
% 2.45/1.02      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(sK2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))))) = k3_subset_1(X0,sK2)
% 2.45/1.02      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 2.45/1.02      inference(theory_normalisation,[status(thm)],[c_219,c_16,c_0]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_717,plain,
% 2.45/1.02      ( k5_xboole_0(sK2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))) = k3_subset_1(X0,sK2)
% 2.45/1.02      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 2.45/1.02      inference(demodulation,[status(thm)],[c_715,c_357]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_779,plain,
% 2.45/1.02      ( k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k3_subset_1(sK1,sK2) ),
% 2.45/1.02      inference(equality_resolution,[status(thm)],[c_717]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1079,plain,
% 2.45/1.02      ( k5_xboole_0(sK2,k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),X0)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
% 2.45/1.02      inference(superposition,[status(thm)],[c_779,c_16]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_8,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))
% 2.45/1.02      | k1_xboole_0 = X0 ),
% 2.45/1.02      inference(cnf_transformation,[],[f92]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_359,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))
% 2.45/1.02      | k1_xboole_0 = X0 ),
% 2.45/1.02      inference(theory_normalisation,[status(thm)],[c_8,c_16,c_0]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_654,plain,
% 2.45/1.02      ( k1_xboole_0 = X0
% 2.45/1.02      | r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1227,plain,
% 2.45/1.02      ( sK2 = k1_xboole_0
% 2.45/1.02      | r1_tarski(sK2,k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2))))) != iProver_top ),
% 2.45/1.02      inference(superposition,[status(thm)],[c_1079,c_654]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1230,plain,
% 2.45/1.02      ( sK2 = k1_xboole_0
% 2.45/1.02      | r1_tarski(sK2,k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) != iProver_top ),
% 2.45/1.02      inference(demodulation,[status(thm)],[c_1227,c_10]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1231,plain,
% 2.45/1.02      ( sK2 = k1_xboole_0
% 2.45/1.02      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
% 2.45/1.02      inference(demodulation,[status(thm)],[c_1230,c_11,c_17,c_18]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1245,plain,
% 2.45/1.02      ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) | sK2 = k1_xboole_0 ),
% 2.45/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1231]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_15,plain,
% 2.45/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.45/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_13,plain,
% 2.45/1.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f101]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_14,plain,
% 2.45/1.02      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_231,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1)
% 2.45/1.02      | v1_xboole_0(X0)
% 2.45/1.02      | k1_xboole_0 != X0
% 2.45/1.02      | k1_xboole_0 != X1 ),
% 2.45/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_14]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_232,plain,
% 2.45/1.02      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) ),
% 2.45/1.02      inference(unflattening,[status(thm)],[c_231]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_36,plain,
% 2.45/1.02      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.45/1.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.45/1.02      | v1_xboole_0(k1_xboole_0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_7,plain,
% 2.45/1.02      ( r1_tarski(X0,X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f100]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_48,plain,
% 2.45/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_234,plain,
% 2.45/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.45/1.02      inference(global_propositional_subsumption,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_232,c_36,c_13,c_48]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_244,plain,
% 2.45/1.02      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.45/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_234]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_245,plain,
% 2.45/1.02      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.45/1.02      inference(unflattening,[status(thm)],[c_244]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1137,plain,
% 2.45/1.02      ( ~ r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),k1_xboole_0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_245]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_363,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_804,plain,
% 2.45/1.02      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_363]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_953,plain,
% 2.45/1.02      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_804]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_954,plain,
% 2.45/1.02      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_953]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_365,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.45/1.02      theory(equality) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_901,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK2) | X2 != X0 | sK2 != X1 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_365]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_903,plain,
% 2.45/1.02      ( r1_tarski(k1_xboole_0,sK2)
% 2.45/1.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.45/1.02      | sK2 != k1_xboole_0
% 2.45/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_901]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_876,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,X2) | X2 != X1 | sK2 != X0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_365]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_878,plain,
% 2.45/1.02      ( r1_tarski(sK2,k1_xboole_0)
% 2.45/1.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.45/1.02      | sK2 != k1_xboole_0
% 2.45/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_876]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_362,plain,( X0 = X0 ),theory(equality) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_799,plain,
% 2.45/1.02      ( sK2 = sK2 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_362]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3,plain,
% 2.45/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.45/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_782,plain,
% 2.45/1.02      ( r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),X0)
% 2.45/1.02      | ~ r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),sK2)
% 2.45/1.02      | ~ r1_tarski(sK2,X0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_784,plain,
% 2.45/1.02      ( ~ r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),sK2)
% 2.45/1.02      | r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),k1_xboole_0)
% 2.45/1.02      | ~ r1_tarski(sK2,k1_xboole_0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_782]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2,plain,
% 2.45/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.45/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_762,plain,
% 2.45/1.02      ( r2_hidden(sK0(sK2,k3_subset_1(sK1,sK2)),sK2)
% 2.45/1.02      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_12,plain,
% 2.45/1.02      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 2.45/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_40,plain,
% 2.45/1.02      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.45/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_20,negated_conjecture,
% 2.45/1.02      ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 != sK2 ),
% 2.45/1.02      inference(cnf_transformation,[],[f97]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_21,negated_conjecture,
% 2.45/1.02      ( r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 = sK2 ),
% 2.45/1.02      inference(cnf_transformation,[],[f98]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(contradiction,plain,
% 2.45/1.02      ( $false ),
% 2.45/1.02      inference(minisat,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_1339,c_1245,c_1137,c_954,c_903,c_878,c_799,c_784,
% 2.45/1.02                 c_762,c_48,c_40,c_13,c_20,c_21]) ).
% 2.45/1.02  
% 2.45/1.02  
% 2.45/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/1.02  
% 2.45/1.02  ------                               Statistics
% 2.45/1.02  
% 2.45/1.02  ------ General
% 2.45/1.02  
% 2.45/1.02  abstr_ref_over_cycles:                  0
% 2.45/1.02  abstr_ref_under_cycles:                 0
% 2.45/1.02  gc_basic_clause_elim:                   0
% 2.45/1.02  forced_gc_time:                         0
% 2.45/1.02  parsing_time:                           0.011
% 2.45/1.02  unif_index_cands_time:                  0.
% 2.45/1.02  unif_index_add_time:                    0.
% 2.45/1.02  orderings_time:                         0.
% 2.45/1.02  out_proof_time:                         0.026
% 2.45/1.02  total_time:                             0.182
% 2.45/1.02  num_of_symbols:                         45
% 2.45/1.02  num_of_terms:                           2362
% 2.45/1.02  
% 2.45/1.02  ------ Preprocessing
% 2.45/1.02  
% 2.45/1.02  num_of_splits:                          0
% 2.45/1.02  num_of_split_atoms:                     0
% 2.45/1.02  num_of_reused_defs:                     0
% 2.45/1.02  num_eq_ax_congr_red:                    8
% 2.45/1.02  num_of_sem_filtered_clauses:            1
% 2.45/1.02  num_of_subtypes:                        0
% 2.45/1.02  monotx_restored_types:                  0
% 2.45/1.02  sat_num_of_epr_types:                   0
% 2.45/1.02  sat_num_of_non_cyclic_types:            0
% 2.45/1.02  sat_guarded_non_collapsed_types:        0
% 2.45/1.02  num_pure_diseq_elim:                    0
% 2.45/1.02  simp_replaced_by:                       0
% 2.45/1.02  res_preprocessed:                       95
% 2.45/1.02  prep_upred:                             0
% 2.45/1.02  prep_unflattend:                        5
% 2.45/1.02  smt_new_axioms:                         0
% 2.45/1.02  pred_elim_cands:                        2
% 2.45/1.02  pred_elim:                              3
% 2.45/1.02  pred_elim_cl:                           4
% 2.45/1.02  pred_elim_cycles:                       5
% 2.45/1.02  merged_defs:                            8
% 2.45/1.02  merged_defs_ncl:                        0
% 2.45/1.02  bin_hyper_res:                          8
% 2.45/1.02  prep_cycles:                            4
% 2.45/1.02  pred_elim_time:                         0.002
% 2.45/1.02  splitting_time:                         0.
% 2.45/1.02  sem_filter_time:                        0.
% 2.45/1.02  monotx_time:                            0.001
% 2.45/1.02  subtype_inf_time:                       0.
% 2.45/1.02  
% 2.45/1.02  ------ Problem properties
% 2.45/1.02  
% 2.45/1.02  clauses:                                18
% 2.45/1.02  conjectures:                            2
% 2.45/1.02  epr:                                    4
% 2.45/1.02  horn:                                   16
% 2.45/1.02  ground:                                 2
% 2.45/1.02  unary:                                  10
% 2.45/1.02  binary:                                 6
% 2.45/1.02  lits:                                   28
% 2.45/1.02  lits_eq:                                14
% 2.45/1.02  fd_pure:                                0
% 2.45/1.02  fd_pseudo:                              0
% 2.45/1.02  fd_cond:                                1
% 2.45/1.02  fd_pseudo_cond:                         1
% 2.45/1.02  ac_symbols:                             1
% 2.45/1.02  
% 2.45/1.02  ------ Propositional Solver
% 2.45/1.02  
% 2.45/1.02  prop_solver_calls:                      26
% 2.45/1.02  prop_fast_solver_calls:                 409
% 2.45/1.02  smt_solver_calls:                       0
% 2.45/1.02  smt_fast_solver_calls:                  0
% 2.45/1.02  prop_num_of_clauses:                    656
% 2.45/1.02  prop_preprocess_simplified:             2640
% 2.45/1.02  prop_fo_subsumed:                       3
% 2.45/1.02  prop_solver_time:                       0.
% 2.45/1.02  smt_solver_time:                        0.
% 2.45/1.02  smt_fast_solver_time:                   0.
% 2.45/1.02  prop_fast_solver_time:                  0.
% 2.45/1.02  prop_unsat_core_time:                   0.
% 2.45/1.02  
% 2.45/1.02  ------ QBF
% 2.45/1.02  
% 2.45/1.02  qbf_q_res:                              0
% 2.45/1.02  qbf_num_tautologies:                    0
% 2.45/1.02  qbf_prep_cycles:                        0
% 2.45/1.02  
% 2.45/1.02  ------ BMC1
% 2.45/1.02  
% 2.45/1.02  bmc1_current_bound:                     -1
% 2.45/1.02  bmc1_last_solved_bound:                 -1
% 2.45/1.02  bmc1_unsat_core_size:                   -1
% 2.45/1.02  bmc1_unsat_core_parents_size:           -1
% 2.45/1.02  bmc1_merge_next_fun:                    0
% 2.45/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.45/1.02  
% 2.45/1.02  ------ Instantiation
% 2.45/1.02  
% 2.45/1.02  inst_num_of_clauses:                    185
% 2.45/1.02  inst_num_in_passive:                    11
% 2.45/1.02  inst_num_in_active:                     108
% 2.45/1.02  inst_num_in_unprocessed:                66
% 2.45/1.02  inst_num_of_loops:                      130
% 2.45/1.02  inst_num_of_learning_restarts:          0
% 2.45/1.02  inst_num_moves_active_passive:          20
% 2.45/1.02  inst_lit_activity:                      0
% 2.45/1.02  inst_lit_activity_moves:                0
% 2.45/1.02  inst_num_tautologies:                   0
% 2.45/1.02  inst_num_prop_implied:                  0
% 2.45/1.02  inst_num_existing_simplified:           0
% 2.45/1.02  inst_num_eq_res_simplified:             0
% 2.45/1.02  inst_num_child_elim:                    0
% 2.45/1.02  inst_num_of_dismatching_blockings:      15
% 2.45/1.02  inst_num_of_non_proper_insts:           122
% 2.45/1.02  inst_num_of_duplicates:                 0
% 2.45/1.02  inst_inst_num_from_inst_to_res:         0
% 2.45/1.02  inst_dismatching_checking_time:         0.
% 2.45/1.02  
% 2.45/1.02  ------ Resolution
% 2.45/1.02  
% 2.45/1.02  res_num_of_clauses:                     0
% 2.45/1.02  res_num_in_passive:                     0
% 2.45/1.02  res_num_in_active:                      0
% 2.45/1.02  res_num_of_loops:                       99
% 2.45/1.02  res_forward_subset_subsumed:            21
% 2.45/1.02  res_backward_subset_subsumed:           0
% 2.45/1.02  res_forward_subsumed:                   0
% 2.45/1.02  res_backward_subsumed:                  0
% 2.45/1.02  res_forward_subsumption_resolution:     0
% 2.45/1.02  res_backward_subsumption_resolution:    0
% 2.45/1.02  res_clause_to_clause_subsumption:       440
% 2.45/1.02  res_orphan_elimination:                 0
% 2.45/1.02  res_tautology_del:                      28
% 2.45/1.02  res_num_eq_res_simplified:              0
% 2.45/1.02  res_num_sel_changes:                    0
% 2.45/1.02  res_moves_from_active_to_pass:          0
% 2.45/1.02  
% 2.45/1.02  ------ Superposition
% 2.45/1.02  
% 2.45/1.02  sup_time_total:                         0.
% 2.45/1.02  sup_time_generating:                    0.
% 2.45/1.02  sup_time_sim_full:                      0.
% 2.45/1.02  sup_time_sim_immed:                     0.
% 2.45/1.02  
% 2.45/1.02  sup_num_of_clauses:                     92
% 2.45/1.02  sup_num_in_active:                      22
% 2.45/1.02  sup_num_in_passive:                     70
% 2.45/1.02  sup_num_of_loops:                       25
% 2.45/1.02  sup_fw_superposition:                   134
% 2.45/1.02  sup_bw_superposition:                   79
% 2.45/1.02  sup_immediate_simplified:               85
% 2.45/1.02  sup_given_eliminated:                   2
% 2.45/1.02  comparisons_done:                       0
% 2.45/1.02  comparisons_avoided:                    0
% 2.45/1.02  
% 2.45/1.02  ------ Simplifications
% 2.45/1.02  
% 2.45/1.02  
% 2.45/1.02  sim_fw_subset_subsumed:                 0
% 2.45/1.02  sim_bw_subset_subsumed:                 0
% 2.45/1.02  sim_fw_subsumed:                        9
% 2.45/1.02  sim_bw_subsumed:                        1
% 2.45/1.02  sim_fw_subsumption_res:                 0
% 2.45/1.02  sim_bw_subsumption_res:                 0
% 2.45/1.02  sim_tautology_del:                      0
% 2.45/1.02  sim_eq_tautology_del:                   13
% 2.45/1.02  sim_eq_res_simp:                        0
% 2.45/1.02  sim_fw_demodulated:                     30
% 2.45/1.02  sim_bw_demodulated:                     14
% 2.45/1.02  sim_light_normalised:                   37
% 2.45/1.02  sim_joinable_taut:                      31
% 2.45/1.02  sim_joinable_simp:                      0
% 2.45/1.02  sim_ac_normalised:                      0
% 2.45/1.02  sim_smt_subsumption:                    0
% 2.45/1.02  
%------------------------------------------------------------------------------
