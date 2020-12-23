%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:21 EST 2020

% Result     : Theorem 27.73s
% Output     : CNFRefutation 27.73s
% Verified   : 
% Statistics : Number of formulae       :  165 (1191 expanded)
%              Number of clauses        :   82 ( 342 expanded)
%              Number of leaves         :   24 ( 267 expanded)
%              Depth                    :   27
%              Number of atoms          :  385 (4097 expanded)
%              Number of equality atoms :  176 (1253 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f58])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f97])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f96])).

fof(f19,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f22,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f107,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f62,f58])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f88])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f89])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f90])).

fof(f99,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f74,f86,f91])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))
      & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f46])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f83,f86])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f98,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f63,f91,f91])).

fof(f85,plain,(
    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1153,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1147,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1146,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1823,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1147,c_1146])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1150,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3596,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_1150])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1151,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3597,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_1151])).

cnf(c_6661,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3596,c_3597])).

cnf(c_6668,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,X2)
    | r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_6661])).

cnf(c_23,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1154,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3307,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
    | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_1154])).

cnf(c_6671,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_6661])).

cnf(c_13592,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3307,c_6671])).

cnf(c_27883,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_6668])).

cnf(c_24,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1136,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1137,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1826,plain,
    ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1137])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_34,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_40,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
    | r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0))
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1233,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_4631,plain,
    ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1826,c_34,c_40,c_1233])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1141,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4637,plain,
    ( r1_tarski(k2_subset_1(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4631,c_1141])).

cnf(c_4642,plain,
    ( k3_xboole_0(k2_subset_1(X0),X0) = k2_subset_1(X0) ),
    inference(superposition,[status(thm)],[c_4637,c_1146])).

cnf(c_4899,plain,
    ( k3_xboole_0(X0,X0) = k2_subset_1(X0) ),
    inference(superposition,[status(thm)],[c_23,c_4642])).

cnf(c_4915,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k2_subset_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4899,c_1150])).

cnf(c_4916,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k2_subset_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4899,c_1151])).

cnf(c_12916,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k2_subset_1(X1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4915,c_4916])).

cnf(c_28157,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k2_subset_1(X0)),k3_xboole_0(k5_xboole_0(X0,k2_subset_1(X0)),X1)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_27883,c_12916])).

cnf(c_18,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_32952,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k2_subset_1(X1)))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_28157,c_18])).

cnf(c_32998,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k2_subset_1(X1)),k3_xboole_0(k5_xboole_0(X1,k2_subset_1(X1)),X0))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_32952,c_18])).

cnf(c_33339,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k2_subset_1(X0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,k2_subset_1(X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13592,c_32998])).

cnf(c_34047,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,k2_subset_1(X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_23,c_33339])).

cnf(c_34061,plain,
    ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_34047,c_6661])).

cnf(c_34457,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_34061])).

cnf(c_34723,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),X0)) = k5_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_6668,c_34457])).

cnf(c_6689,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_6671])).

cnf(c_34717,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6689,c_34457])).

cnf(c_38262,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_34717,c_18])).

cnf(c_38490,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),X0))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_38262,c_18])).

cnf(c_54143,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X1)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_34723,c_38490])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1132,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1828,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1137])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_36,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1242,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
    | r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1243,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_4243,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1828,c_30,c_36,c_1243])).

cnf(c_4248,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4243,c_1141])).

cnf(c_4314,plain,
    ( k3_xboole_0(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_4248,c_1146])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1133,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1592,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k2_subset_1(X1),k3_xboole_0(k2_subset_1(X1),X0))) = k4_subset_1(X1,X0,k2_subset_1(X1))
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1133])).

cnf(c_3874,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k2_subset_1(sK3),k3_xboole_0(k2_subset_1(sK3),sK4))) = k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(superposition,[status(thm)],[c_1132,c_1592])).

cnf(c_8616,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(superposition,[status(thm)],[c_23,c_3874])).

cnf(c_13,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1349,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_13,c_18])).

cnf(c_2522,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1349,c_18])).

cnf(c_8982,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK4,sK3))) = k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(superposition,[status(thm)],[c_8616,c_2522])).

cnf(c_9167,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k5_xboole_0(sK3,k5_xboole_0(sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_4314,c_8982])).

cnf(c_28,negated_conjecture,
    ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_91822,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,sK4)) != k2_subset_1(sK3) ),
    inference(superposition,[status(thm)],[c_9167,c_28])).

cnf(c_91827,plain,
    ( k5_xboole_0(sK3,k1_xboole_0) != k2_subset_1(sK3) ),
    inference(superposition,[status(thm)],[c_54143,c_91822])).

cnf(c_92049,plain,
    ( k2_subset_1(sK3) != sK3 ),
    inference(superposition,[status(thm)],[c_11,c_91827])).

cnf(c_43,plain,
    ( k2_subset_1(sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_92049,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.73/4.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.73/4.03  
% 27.73/4.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.73/4.03  
% 27.73/4.03  ------  iProver source info
% 27.73/4.03  
% 27.73/4.03  git: date: 2020-06-30 10:37:57 +0100
% 27.73/4.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.73/4.03  git: non_committed_changes: false
% 27.73/4.03  git: last_make_outside_of_git: false
% 27.73/4.03  
% 27.73/4.03  ------ 
% 27.73/4.03  ------ Parsing...
% 27.73/4.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.73/4.03  
% 27.73/4.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.73/4.03  
% 27.73/4.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.73/4.03  
% 27.73/4.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.73/4.03  ------ Proving...
% 27.73/4.03  ------ Problem Properties 
% 27.73/4.03  
% 27.73/4.03  
% 27.73/4.03  clauses                                 29
% 27.73/4.03  conjectures                             2
% 27.73/4.03  EPR                                     8
% 27.73/4.03  Horn                                    22
% 27.73/4.03  unary                                   11
% 27.73/4.03  binary                                  5
% 27.73/4.03  lits                                    61
% 27.73/4.03  lits eq                                 14
% 27.73/4.03  fd_pure                                 0
% 27.73/4.03  fd_pseudo                               0
% 27.73/4.03  fd_cond                                 0
% 27.73/4.03  fd_pseudo_cond                          7
% 27.73/4.03  AC symbols                              0
% 27.73/4.03  
% 27.73/4.03  ------ Input Options Time Limit: Unbounded
% 27.73/4.03  
% 27.73/4.03  
% 27.73/4.03  ------ 
% 27.73/4.03  Current options:
% 27.73/4.03  ------ 
% 27.73/4.03  
% 27.73/4.03  
% 27.73/4.03  
% 27.73/4.03  
% 27.73/4.03  ------ Proving...
% 27.73/4.03  
% 27.73/4.03  
% 27.73/4.03  % SZS status Theorem for theBenchmark.p
% 27.73/4.03  
% 27.73/4.03  % SZS output start CNFRefutation for theBenchmark.p
% 27.73/4.03  
% 27.73/4.03  fof(f6,axiom,(
% 27.73/4.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f60,plain,(
% 27.73/4.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.73/4.03    inference(cnf_transformation,[],[f6])).
% 27.73/4.03  
% 27.73/4.03  fof(f1,axiom,(
% 27.73/4.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f32,plain,(
% 27.73/4.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.73/4.03    inference(nnf_transformation,[],[f1])).
% 27.73/4.03  
% 27.73/4.03  fof(f33,plain,(
% 27.73/4.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.73/4.03    inference(flattening,[],[f32])).
% 27.73/4.03  
% 27.73/4.03  fof(f34,plain,(
% 27.73/4.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.73/4.03    inference(rectify,[],[f33])).
% 27.73/4.03  
% 27.73/4.03  fof(f35,plain,(
% 27.73/4.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 27.73/4.03    introduced(choice_axiom,[])).
% 27.73/4.03  
% 27.73/4.03  fof(f36,plain,(
% 27.73/4.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.73/4.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 27.73/4.03  
% 27.73/4.03  fof(f51,plain,(
% 27.73/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f36])).
% 27.73/4.03  
% 27.73/4.03  fof(f4,axiom,(
% 27.73/4.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f58,plain,(
% 27.73/4.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.73/4.03    inference(cnf_transformation,[],[f4])).
% 27.73/4.03  
% 27.73/4.03  fof(f94,plain,(
% 27.73/4.03    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 27.73/4.03    inference(definition_unfolding,[],[f51,f58])).
% 27.73/4.03  
% 27.73/4.03  fof(f3,axiom,(
% 27.73/4.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f37,plain,(
% 27.73/4.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.73/4.03    inference(nnf_transformation,[],[f3])).
% 27.73/4.03  
% 27.73/4.03  fof(f38,plain,(
% 27.73/4.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.73/4.03    inference(flattening,[],[f37])).
% 27.73/4.03  
% 27.73/4.03  fof(f55,plain,(
% 27.73/4.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.73/4.03    inference(cnf_transformation,[],[f38])).
% 27.73/4.03  
% 27.73/4.03  fof(f105,plain,(
% 27.73/4.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.73/4.03    inference(equality_resolution,[],[f55])).
% 27.73/4.03  
% 27.73/4.03  fof(f5,axiom,(
% 27.73/4.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f26,plain,(
% 27.73/4.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 27.73/4.03    inference(ennf_transformation,[],[f5])).
% 27.73/4.03  
% 27.73/4.03  fof(f59,plain,(
% 27.73/4.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f26])).
% 27.73/4.03  
% 27.73/4.03  fof(f48,plain,(
% 27.73/4.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 27.73/4.03    inference(cnf_transformation,[],[f36])).
% 27.73/4.03  
% 27.73/4.03  fof(f97,plain,(
% 27.73/4.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 27.73/4.03    inference(definition_unfolding,[],[f48,f58])).
% 27.73/4.03  
% 27.73/4.03  fof(f103,plain,(
% 27.73/4.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 27.73/4.03    inference(equality_resolution,[],[f97])).
% 27.73/4.03  
% 27.73/4.03  fof(f49,plain,(
% 27.73/4.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 27.73/4.03    inference(cnf_transformation,[],[f36])).
% 27.73/4.03  
% 27.73/4.03  fof(f96,plain,(
% 27.73/4.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 27.73/4.03    inference(definition_unfolding,[],[f49,f58])).
% 27.73/4.03  
% 27.73/4.03  fof(f102,plain,(
% 27.73/4.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 27.73/4.03    inference(equality_resolution,[],[f96])).
% 27.73/4.03  
% 27.73/4.03  fof(f19,axiom,(
% 27.73/4.03    ! [X0] : k2_subset_1(X0) = X0),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f79,plain,(
% 27.73/4.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 27.73/4.03    inference(cnf_transformation,[],[f19])).
% 27.73/4.03  
% 27.73/4.03  fof(f52,plain,(
% 27.73/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f36])).
% 27.73/4.03  
% 27.73/4.03  fof(f93,plain,(
% 27.73/4.03    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 27.73/4.03    inference(definition_unfolding,[],[f52,f58])).
% 27.73/4.03  
% 27.73/4.03  fof(f20,axiom,(
% 27.73/4.03    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f80,plain,(
% 27.73/4.03    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 27.73/4.03    inference(cnf_transformation,[],[f20])).
% 27.73/4.03  
% 27.73/4.03  fof(f18,axiom,(
% 27.73/4.03    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f28,plain,(
% 27.73/4.03    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 27.73/4.03    inference(ennf_transformation,[],[f18])).
% 27.73/4.03  
% 27.73/4.03  fof(f43,plain,(
% 27.73/4.03    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 27.73/4.03    inference(nnf_transformation,[],[f28])).
% 27.73/4.03  
% 27.73/4.03  fof(f75,plain,(
% 27.73/4.03    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f43])).
% 27.73/4.03  
% 27.73/4.03  fof(f22,axiom,(
% 27.73/4.03    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f82,plain,(
% 27.73/4.03    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 27.73/4.03    inference(cnf_transformation,[],[f22])).
% 27.73/4.03  
% 27.73/4.03  fof(f16,axiom,(
% 27.73/4.03    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f39,plain,(
% 27.73/4.03    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 27.73/4.03    inference(nnf_transformation,[],[f16])).
% 27.73/4.03  
% 27.73/4.03  fof(f40,plain,(
% 27.73/4.03    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 27.73/4.03    inference(rectify,[],[f39])).
% 27.73/4.03  
% 27.73/4.03  fof(f41,plain,(
% 27.73/4.03    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 27.73/4.03    introduced(choice_axiom,[])).
% 27.73/4.03  
% 27.73/4.03  fof(f42,plain,(
% 27.73/4.03    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 27.73/4.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 27.73/4.03  
% 27.73/4.03  fof(f70,plain,(
% 27.73/4.03    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 27.73/4.03    inference(cnf_transformation,[],[f42])).
% 27.73/4.03  
% 27.73/4.03  fof(f107,plain,(
% 27.73/4.03    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 27.73/4.03    inference(equality_resolution,[],[f70])).
% 27.73/4.03  
% 27.73/4.03  fof(f17,axiom,(
% 27.73/4.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f74,plain,(
% 27.73/4.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 27.73/4.03    inference(cnf_transformation,[],[f17])).
% 27.73/4.03  
% 27.73/4.03  fof(f8,axiom,(
% 27.73/4.03    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f62,plain,(
% 27.73/4.03    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f8])).
% 27.73/4.03  
% 27.73/4.03  fof(f86,plain,(
% 27.73/4.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 27.73/4.03    inference(definition_unfolding,[],[f62,f58])).
% 27.73/4.03  
% 27.73/4.03  fof(f10,axiom,(
% 27.73/4.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f64,plain,(
% 27.73/4.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f10])).
% 27.73/4.03  
% 27.73/4.03  fof(f11,axiom,(
% 27.73/4.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f65,plain,(
% 27.73/4.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f11])).
% 27.73/4.03  
% 27.73/4.03  fof(f12,axiom,(
% 27.73/4.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f66,plain,(
% 27.73/4.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f12])).
% 27.73/4.03  
% 27.73/4.03  fof(f13,axiom,(
% 27.73/4.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f67,plain,(
% 27.73/4.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f13])).
% 27.73/4.03  
% 27.73/4.03  fof(f14,axiom,(
% 27.73/4.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f68,plain,(
% 27.73/4.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f14])).
% 27.73/4.03  
% 27.73/4.03  fof(f15,axiom,(
% 27.73/4.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f69,plain,(
% 27.73/4.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f15])).
% 27.73/4.03  
% 27.73/4.03  fof(f87,plain,(
% 27.73/4.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 27.73/4.03    inference(definition_unfolding,[],[f68,f69])).
% 27.73/4.03  
% 27.73/4.03  fof(f88,plain,(
% 27.73/4.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 27.73/4.03    inference(definition_unfolding,[],[f67,f87])).
% 27.73/4.03  
% 27.73/4.03  fof(f89,plain,(
% 27.73/4.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.73/4.03    inference(definition_unfolding,[],[f66,f88])).
% 27.73/4.03  
% 27.73/4.03  fof(f90,plain,(
% 27.73/4.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 27.73/4.03    inference(definition_unfolding,[],[f65,f89])).
% 27.73/4.03  
% 27.73/4.03  fof(f91,plain,(
% 27.73/4.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 27.73/4.03    inference(definition_unfolding,[],[f64,f90])).
% 27.73/4.03  
% 27.73/4.03  fof(f99,plain,(
% 27.73/4.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 27.73/4.03    inference(definition_unfolding,[],[f74,f86,f91])).
% 27.73/4.03  
% 27.73/4.03  fof(f24,conjecture,(
% 27.73/4.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f25,negated_conjecture,(
% 27.73/4.03    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 27.73/4.03    inference(negated_conjecture,[],[f24])).
% 27.73/4.03  
% 27.73/4.03  fof(f31,plain,(
% 27.73/4.03    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.73/4.03    inference(ennf_transformation,[],[f25])).
% 27.73/4.03  
% 27.73/4.03  fof(f46,plain,(
% 27.73/4.03    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 27.73/4.03    introduced(choice_axiom,[])).
% 27.73/4.03  
% 27.73/4.03  fof(f47,plain,(
% 27.73/4.03    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 27.73/4.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f46])).
% 27.73/4.03  
% 27.73/4.03  fof(f84,plain,(
% 27.73/4.03    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 27.73/4.03    inference(cnf_transformation,[],[f47])).
% 27.73/4.03  
% 27.73/4.03  fof(f23,axiom,(
% 27.73/4.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f29,plain,(
% 27.73/4.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 27.73/4.03    inference(ennf_transformation,[],[f23])).
% 27.73/4.03  
% 27.73/4.03  fof(f30,plain,(
% 27.73/4.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.73/4.03    inference(flattening,[],[f29])).
% 27.73/4.03  
% 27.73/4.03  fof(f83,plain,(
% 27.73/4.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.73/4.03    inference(cnf_transformation,[],[f30])).
% 27.73/4.03  
% 27.73/4.03  fof(f100,plain,(
% 27.73/4.03    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.73/4.03    inference(definition_unfolding,[],[f83,f86])).
% 27.73/4.03  
% 27.73/4.03  fof(f9,axiom,(
% 27.73/4.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 27.73/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/4.03  
% 27.73/4.03  fof(f63,plain,(
% 27.73/4.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 27.73/4.03    inference(cnf_transformation,[],[f9])).
% 27.73/4.03  
% 27.73/4.03  fof(f98,plain,(
% 27.73/4.03    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 27.73/4.03    inference(definition_unfolding,[],[f63,f91,f91])).
% 27.73/4.03  
% 27.73/4.03  fof(f85,plain,(
% 27.73/4.03    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))),
% 27.73/4.03    inference(cnf_transformation,[],[f47])).
% 27.73/4.03  
% 27.73/4.03  cnf(c_11,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.73/4.03      inference(cnf_transformation,[],[f60]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_2,plain,
% 27.73/4.03      ( r2_hidden(sK0(X0,X1,X2),X0)
% 27.73/4.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 27.73/4.03      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 27.73/4.03      inference(cnf_transformation,[],[f94]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1153,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 27.73/4.03      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 27.73/4.03      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_9,plain,
% 27.73/4.03      ( r1_tarski(X0,X0) ),
% 27.73/4.03      inference(cnf_transformation,[],[f105]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1147,plain,
% 27.73/4.03      ( r1_tarski(X0,X0) = iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_10,plain,
% 27.73/4.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 27.73/4.03      inference(cnf_transformation,[],[f59]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1146,plain,
% 27.73/4.03      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1823,plain,
% 27.73/4.03      ( k3_xboole_0(X0,X0) = X0 ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1147,c_1146]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_5,plain,
% 27.73/4.03      ( r2_hidden(X0,X1)
% 27.73/4.03      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 27.73/4.03      inference(cnf_transformation,[],[f103]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1150,plain,
% 27.73/4.03      ( r2_hidden(X0,X1) = iProver_top
% 27.73/4.03      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_3596,plain,
% 27.73/4.03      ( r2_hidden(X0,X1) = iProver_top
% 27.73/4.03      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1823,c_1150]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_4,plain,
% 27.73/4.03      ( ~ r2_hidden(X0,X1)
% 27.73/4.03      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 27.73/4.03      inference(cnf_transformation,[],[f102]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1151,plain,
% 27.73/4.03      ( r2_hidden(X0,X1) != iProver_top
% 27.73/4.03      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_3597,plain,
% 27.73/4.03      ( r2_hidden(X0,X1) != iProver_top
% 27.73/4.03      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1823,c_1151]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_6661,plain,
% 27.73/4.03      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 27.73/4.03      inference(global_propositional_subsumption,
% 27.73/4.03                [status(thm)],
% 27.73/4.03                [c_3596,c_3597]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_6668,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,X2)
% 27.73/4.03      | r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X2)),X0) = iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1153,c_6661]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_23,plain,
% 27.73/4.03      ( k2_subset_1(X0) = X0 ),
% 27.73/4.03      inference(cnf_transformation,[],[f79]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1,plain,
% 27.73/4.03      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 27.73/4.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 27.73/4.03      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 27.73/4.03      inference(cnf_transformation,[],[f93]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1154,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 27.73/4.03      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 27.73/4.03      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_3307,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
% 27.73/4.03      | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1153,c_1154]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_6671,plain,
% 27.73/4.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_11,c_6661]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_13592,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_3307,c_6671]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_27883,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 27.73/4.03      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_11,c_6668]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_24,plain,
% 27.73/4.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 27.73/4.03      inference(cnf_transformation,[],[f80]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1136,plain,
% 27.73/4.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_22,plain,
% 27.73/4.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 27.73/4.03      inference(cnf_transformation,[],[f75]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1137,plain,
% 27.73/4.03      ( m1_subset_1(X0,X1) != iProver_top
% 27.73/4.03      | r2_hidden(X0,X1) = iProver_top
% 27.73/4.03      | v1_xboole_0(X1) = iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1826,plain,
% 27.73/4.03      ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top
% 27.73/4.03      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1136,c_1137]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_26,plain,
% 27.73/4.03      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 27.73/4.03      inference(cnf_transformation,[],[f82]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_34,plain,
% 27.73/4.03      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_40,plain,
% 27.73/4.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1232,plain,
% 27.73/4.03      ( ~ m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
% 27.73/4.03      | r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0))
% 27.73/4.03      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 27.73/4.03      inference(instantiation,[status(thm)],[c_22]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1233,plain,
% 27.73/4.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) != iProver_top
% 27.73/4.03      | r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top
% 27.73/4.03      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_1232]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_4631,plain,
% 27.73/4.03      ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 27.73/4.03      inference(global_propositional_subsumption,
% 27.73/4.03                [status(thm)],
% 27.73/4.03                [c_1826,c_34,c_40,c_1233]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_17,plain,
% 27.73/4.03      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 27.73/4.03      inference(cnf_transformation,[],[f107]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1141,plain,
% 27.73/4.03      ( r1_tarski(X0,X1) = iProver_top
% 27.73/4.03      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_4637,plain,
% 27.73/4.03      ( r1_tarski(k2_subset_1(X0),X0) = iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_4631,c_1141]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_4642,plain,
% 27.73/4.03      ( k3_xboole_0(k2_subset_1(X0),X0) = k2_subset_1(X0) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_4637,c_1146]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_4899,plain,
% 27.73/4.03      ( k3_xboole_0(X0,X0) = k2_subset_1(X0) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_23,c_4642]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_4915,plain,
% 27.73/4.03      ( r2_hidden(X0,X1) = iProver_top
% 27.73/4.03      | r2_hidden(X0,k5_xboole_0(X1,k2_subset_1(X1))) != iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_4899,c_1150]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_4916,plain,
% 27.73/4.03      ( r2_hidden(X0,X1) != iProver_top
% 27.73/4.03      | r2_hidden(X0,k5_xboole_0(X1,k2_subset_1(X1))) != iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_4899,c_1151]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_12916,plain,
% 27.73/4.03      ( r2_hidden(X0,k5_xboole_0(X1,k2_subset_1(X1))) != iProver_top ),
% 27.73/4.03      inference(global_propositional_subsumption,
% 27.73/4.03                [status(thm)],
% 27.73/4.03                [c_4915,c_4916]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_28157,plain,
% 27.73/4.03      ( k5_xboole_0(k5_xboole_0(X0,k2_subset_1(X0)),k3_xboole_0(k5_xboole_0(X0,k2_subset_1(X0)),X1)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_27883,c_12916]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_18,plain,
% 27.73/4.03      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 27.73/4.03      inference(cnf_transformation,[],[f99]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_32952,plain,
% 27.73/4.03      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k2_subset_1(X1)))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_28157,c_18]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_32998,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k2_subset_1(X1)),k3_xboole_0(k5_xboole_0(X1,k2_subset_1(X1)),X0))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_32952,c_18]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_33339,plain,
% 27.73/4.03      ( k5_xboole_0(k5_xboole_0(X0,k2_subset_1(X0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,k2_subset_1(X0)),k1_xboole_0) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_13592,c_32998]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_34047,plain,
% 27.73/4.03      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,k2_subset_1(X0)),k1_xboole_0) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_23,c_33339]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_34061,plain,
% 27.73/4.03      ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),k1_xboole_0)) != iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_34047,c_6661]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_34457,plain,
% 27.73/4.03      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0))) != iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_11,c_34061]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_34723,plain,
% 27.73/4.03      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),X0)) = k5_xboole_0(X1,X1) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_6668,c_34457]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_6689,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 27.73/4.03      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1153,c_6671]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_34717,plain,
% 27.73/4.03      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),X0)) = k1_xboole_0 ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_6689,c_34457]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_38262,plain,
% 27.73/4.03      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)))) = k5_xboole_0(X0,k1_xboole_0) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_34717,c_18]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_38490,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k2_subset_1(k1_xboole_0)),X0))) = k5_xboole_0(X0,k1_xboole_0) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_38262,c_18]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_54143,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k5_xboole_0(X1,X1)) = k5_xboole_0(X0,k1_xboole_0) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_34723,c_38490]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_29,negated_conjecture,
% 27.73/4.03      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 27.73/4.03      inference(cnf_transformation,[],[f84]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1132,plain,
% 27.73/4.03      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1828,plain,
% 27.73/4.03      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
% 27.73/4.03      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1132,c_1137]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_30,plain,
% 27.73/4.03      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_36,plain,
% 27.73/4.03      ( v1_xboole_0(k1_zfmisc_1(sK3)) != iProver_top ),
% 27.73/4.03      inference(instantiation,[status(thm)],[c_34]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1242,plain,
% 27.73/4.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
% 27.73/4.03      | r2_hidden(sK4,k1_zfmisc_1(sK3))
% 27.73/4.03      | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 27.73/4.03      inference(instantiation,[status(thm)],[c_22]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1243,plain,
% 27.73/4.03      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top
% 27.73/4.03      | r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
% 27.73/4.03      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_4243,plain,
% 27.73/4.03      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 27.73/4.03      inference(global_propositional_subsumption,
% 27.73/4.03                [status(thm)],
% 27.73/4.03                [c_1828,c_30,c_36,c_1243]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_4248,plain,
% 27.73/4.03      ( r1_tarski(sK4,sK3) = iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_4243,c_1141]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_4314,plain,
% 27.73/4.03      ( k3_xboole_0(sK4,sK3) = sK4 ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_4248,c_1146]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_27,plain,
% 27.73/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.73/4.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.73/4.03      | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
% 27.73/4.03      inference(cnf_transformation,[],[f100]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1133,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
% 27.73/4.03      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 27.73/4.03      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 27.73/4.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1592,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k5_xboole_0(k2_subset_1(X1),k3_xboole_0(k2_subset_1(X1),X0))) = k4_subset_1(X1,X0,k2_subset_1(X1))
% 27.73/4.03      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1136,c_1133]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_3874,plain,
% 27.73/4.03      ( k5_xboole_0(sK4,k5_xboole_0(k2_subset_1(sK3),k3_xboole_0(k2_subset_1(sK3),sK4))) = k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1132,c_1592]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_8616,plain,
% 27.73/4.03      ( k5_xboole_0(sK4,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_23,c_3874]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_13,plain,
% 27.73/4.03      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 27.73/4.03      inference(cnf_transformation,[],[f98]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_1349,plain,
% 27.73/4.03      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_13,c_18]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_2522,plain,
% 27.73/4.03      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_1349,c_18]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_8982,plain,
% 27.73/4.03      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK4,sK3))) = k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_8616,c_2522]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_9167,plain,
% 27.73/4.03      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k5_xboole_0(sK3,k5_xboole_0(sK4,sK4)) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_4314,c_8982]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_28,negated_conjecture,
% 27.73/4.03      ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
% 27.73/4.03      inference(cnf_transformation,[],[f85]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_91822,plain,
% 27.73/4.03      ( k5_xboole_0(sK3,k5_xboole_0(sK4,sK4)) != k2_subset_1(sK3) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_9167,c_28]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_91827,plain,
% 27.73/4.03      ( k5_xboole_0(sK3,k1_xboole_0) != k2_subset_1(sK3) ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_54143,c_91822]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_92049,plain,
% 27.73/4.03      ( k2_subset_1(sK3) != sK3 ),
% 27.73/4.03      inference(superposition,[status(thm)],[c_11,c_91827]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(c_43,plain,
% 27.73/4.03      ( k2_subset_1(sK3) = sK3 ),
% 27.73/4.03      inference(instantiation,[status(thm)],[c_23]) ).
% 27.73/4.03  
% 27.73/4.03  cnf(contradiction,plain,
% 27.73/4.03      ( $false ),
% 27.73/4.03      inference(minisat,[status(thm)],[c_92049,c_43]) ).
% 27.73/4.03  
% 27.73/4.03  
% 27.73/4.03  % SZS output end CNFRefutation for theBenchmark.p
% 27.73/4.03  
% 27.73/4.03  ------                               Statistics
% 27.73/4.03  
% 27.73/4.03  ------ Selected
% 27.73/4.03  
% 27.73/4.03  total_time:                             3.141
% 27.73/4.03  
%------------------------------------------------------------------------------
