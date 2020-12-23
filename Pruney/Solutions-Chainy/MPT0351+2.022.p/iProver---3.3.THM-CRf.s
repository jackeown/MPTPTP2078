%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:22 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 355 expanded)
%              Number of clauses        :   69 ( 105 expanded)
%              Number of leaves         :   23 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :  385 (1066 expanded)
%              Number of equality atoms :  134 ( 307 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4))
      & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f46])).

fof(f80,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f82])).

fof(f86,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f61,f83,f83])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f79,f83])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f59,f83])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f87,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f65,f82,f82])).

fof(f81,plain,(
    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_840,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_26,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_827,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_854,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_827,c_25])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_828,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1655,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_828])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_844,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_845,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2155,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_844,c_845])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_832,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_846,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1635,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_846])).

cnf(c_5130,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_1635])).

cnf(c_6376,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1655,c_5130])).

cnf(c_14,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_838,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2430,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_838])).

cnf(c_6383,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6376,c_2430])).

cnf(c_6396,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = X1
    | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_6383])).

cnf(c_6409,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6396,c_14])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_825,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1654,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_828])).

cnf(c_1134,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(resolution,[status(thm)],[c_24,c_29])).

cnf(c_52,plain,
    ( ~ r1_tarski(sK4,sK4)
    | r2_hidden(sK4,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_84,plain,
    ( r1_tarski(sK4,sK4)
    | r2_hidden(sK1(sK4,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_87,plain,
    ( r1_tarski(sK4,sK4)
    | ~ r2_hidden(sK1(sK4,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1079,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1081,plain,
    ( ~ r2_hidden(sK4,k1_zfmisc_1(sK4))
    | ~ v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_1137,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1134,c_52,c_84,c_87,c_1081])).

cnf(c_1139,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_5859,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1654,c_1139])).

cnf(c_20,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_831,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5867,plain,
    ( r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5859,c_831])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_836,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6144,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) = sK5 ),
    inference(superposition,[status(thm)],[c_5867,c_836])).

cnf(c_7355,plain,
    ( r2_hidden(X0,k4_xboole_0(sK5,sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6144,c_838])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_837,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_10281,plain,
    ( r2_hidden(X0,k4_xboole_0(sK5,sK4)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7355,c_837])).

cnf(c_10293,plain,
    ( k4_xboole_0(sK5,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6409,c_10281])).

cnf(c_13,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_10655,plain,
    ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = k3_tarski(k2_enumset1(sK4,sK4,sK4,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_10293,c_13])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k2_enumset1(X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_826,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1269,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,sK5)) = k4_subset_1(sK4,X0,sK5)
    | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_826])).

cnf(c_3806,plain,
    ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = k4_subset_1(sK4,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_854,c_1269])).

cnf(c_10657,plain,
    ( k3_tarski(k2_enumset1(sK4,sK4,sK4,k1_xboole_0)) = k4_subset_1(sK4,sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_10655,c_3806])).

cnf(c_11,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_10658,plain,
    ( k4_subset_1(sK4,sK4,sK5) = sK4 ),
    inference(demodulation,[status(thm)],[c_10657,c_11])).

cnf(c_16,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1270,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X1,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_826])).

cnf(c_4126,plain,
    ( k3_tarski(k2_enumset1(sK5,sK5,sK5,sK4)) = k4_subset_1(sK4,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_825,c_1270])).

cnf(c_5137,plain,
    ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = k4_subset_1(sK4,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_16,c_4126])).

cnf(c_5140,plain,
    ( k4_subset_1(sK4,sK4,sK5) = k4_subset_1(sK4,sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_5137,c_3806])).

cnf(c_28,negated_conjecture,
    ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_859,plain,
    ( k4_subset_1(sK4,sK5,sK4) != sK4 ),
    inference(demodulation,[status(thm)],[c_28,c_25])).

cnf(c_5248,plain,
    ( k4_subset_1(sK4,sK4,sK5) != sK4 ),
    inference(demodulation,[status(thm)],[c_5140,c_859])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10658,c_5248])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.59/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/1.00  
% 3.59/1.00  ------  iProver source info
% 3.59/1.00  
% 3.59/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.59/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/1.00  git: non_committed_changes: false
% 3.59/1.00  git: last_make_outside_of_git: false
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    --mode clausify
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             sel
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         604.99
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              none
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           false
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             false
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         false
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     num_symb
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       true
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.00  --res_passive_queues_freq               [15;5]
% 3.59/1.00  --res_forward_subs                      full
% 3.59/1.00  --res_backward_subs                     full
% 3.59/1.00  --res_forward_subs_resolution           true
% 3.59/1.00  --res_backward_subs_resolution          true
% 3.59/1.00  --res_orphan_elimination                true
% 3.59/1.00  --res_time_limit                        2.
% 3.59/1.00  --res_out_proof                         true
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Options
% 3.59/1.00  
% 3.59/1.00  --superposition_flag                    true
% 3.59/1.00  --sup_passive_queue_type                priority_queues
% 3.59/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.00  --sup_passive_queues_freq               [1;4]
% 3.59/1.00  --demod_completeness_check              fast
% 3.59/1.00  --demod_use_ground                      true
% 3.59/1.00  --sup_to_prop_solver                    passive
% 3.59/1.00  --sup_prop_simpl_new                    true
% 3.59/1.00  --sup_prop_simpl_given                  true
% 3.59/1.00  --sup_fun_splitting                     false
% 3.59/1.00  --sup_smt_interval                      50000
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Simplification Setup
% 3.59/1.00  
% 3.59/1.00  --sup_indices_passive                   []
% 3.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_full_bw                           [BwDemod]
% 3.59/1.00  --sup_immed_triv                        [TrivRules]
% 3.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_immed_bw_main                     []
% 3.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  
% 3.59/1.00  ------ Combination Options
% 3.59/1.00  
% 3.59/1.00  --comb_res_mult                         3
% 3.59/1.00  --comb_sup_mult                         2
% 3.59/1.00  --comb_inst_mult                        10
% 3.59/1.00  
% 3.59/1.00  ------ Debug Options
% 3.59/1.00  
% 3.59/1.00  --dbg_backtrace                         false
% 3.59/1.00  --dbg_dump_prop_clauses                 false
% 3.59/1.00  --dbg_dump_prop_clauses_file            -
% 3.59/1.00  --dbg_out_stat                          false
% 3.59/1.00  ------ Parsing...
% 3.59/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/1.00  ------ Proving...
% 3.59/1.00  ------ Problem Properties 
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  clauses                                 30
% 3.59/1.00  conjectures                             2
% 3.59/1.00  EPR                                     7
% 3.59/1.00  Horn                                    22
% 3.59/1.00  unary                                   8
% 3.59/1.00  binary                                  10
% 3.59/1.00  lits                                    65
% 3.59/1.00  lits eq                                 14
% 3.59/1.00  fd_pure                                 0
% 3.59/1.00  fd_pseudo                               0
% 3.59/1.00  fd_cond                                 0
% 3.59/1.00  fd_pseudo_cond                          6
% 3.59/1.00  AC symbols                              0
% 3.59/1.00  
% 3.59/1.00  ------ Input Options Time Limit: Unbounded
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  Current options:
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    --mode clausify
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             sel
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         604.99
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              none
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           false
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             false
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         false
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     num_symb
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       true
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.00  --res_passive_queues_freq               [15;5]
% 3.59/1.00  --res_forward_subs                      full
% 3.59/1.00  --res_backward_subs                     full
% 3.59/1.00  --res_forward_subs_resolution           true
% 3.59/1.00  --res_backward_subs_resolution          true
% 3.59/1.00  --res_orphan_elimination                true
% 3.59/1.00  --res_time_limit                        2.
% 3.59/1.00  --res_out_proof                         true
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Options
% 3.59/1.00  
% 3.59/1.00  --superposition_flag                    true
% 3.59/1.00  --sup_passive_queue_type                priority_queues
% 3.59/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.00  --sup_passive_queues_freq               [1;4]
% 3.59/1.00  --demod_completeness_check              fast
% 3.59/1.00  --demod_use_ground                      true
% 3.59/1.00  --sup_to_prop_solver                    passive
% 3.59/1.00  --sup_prop_simpl_new                    true
% 3.59/1.00  --sup_prop_simpl_given                  true
% 3.59/1.00  --sup_fun_splitting                     false
% 3.59/1.00  --sup_smt_interval                      50000
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Simplification Setup
% 3.59/1.00  
% 3.59/1.00  --sup_indices_passive                   []
% 3.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_full_bw                           [BwDemod]
% 3.59/1.00  --sup_immed_triv                        [TrivRules]
% 3.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_immed_bw_main                     []
% 3.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  
% 3.59/1.00  ------ Combination Options
% 3.59/1.00  
% 3.59/1.00  --comb_res_mult                         3
% 3.59/1.00  --comb_sup_mult                         2
% 3.59/1.00  --comb_inst_mult                        10
% 3.59/1.00  
% 3.59/1.00  ------ Debug Options
% 3.59/1.00  
% 3.59/1.00  --dbg_backtrace                         false
% 3.59/1.00  --dbg_dump_prop_clauses                 false
% 3.59/1.00  --dbg_dump_prop_clauses_file            -
% 3.59/1.00  --dbg_out_stat                          false
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  ------ Proving...
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  % SZS status Theorem for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  fof(f3,axiom,(
% 3.59/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f36,plain,(
% 3.59/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.59/1.00    inference(nnf_transformation,[],[f3])).
% 3.59/1.00  
% 3.59/1.00  fof(f37,plain,(
% 3.59/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.59/1.00    inference(flattening,[],[f36])).
% 3.59/1.00  
% 3.59/1.00  fof(f38,plain,(
% 3.59/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.59/1.00    inference(rectify,[],[f37])).
% 3.59/1.00  
% 3.59/1.00  fof(f39,plain,(
% 3.59/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f40,plain,(
% 3.59/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 3.59/1.00  
% 3.59/1.00  fof(f56,plain,(
% 3.59/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f40])).
% 3.59/1.00  
% 3.59/1.00  fof(f17,axiom,(
% 3.59/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f78,plain,(
% 3.59/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.59/1.00    inference(cnf_transformation,[],[f17])).
% 3.59/1.00  
% 3.59/1.00  fof(f16,axiom,(
% 3.59/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f77,plain,(
% 3.59/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.59/1.00    inference(cnf_transformation,[],[f16])).
% 3.59/1.00  
% 3.59/1.00  fof(f15,axiom,(
% 3.59/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f24,plain,(
% 3.59/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f15])).
% 3.59/1.00  
% 3.59/1.00  fof(f45,plain,(
% 3.59/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.59/1.00    inference(nnf_transformation,[],[f24])).
% 3.59/1.00  
% 3.59/1.00  fof(f73,plain,(
% 3.59/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f45])).
% 3.59/1.00  
% 3.59/1.00  fof(f2,axiom,(
% 3.59/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f21,plain,(
% 3.59/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f2])).
% 3.59/1.00  
% 3.59/1.00  fof(f32,plain,(
% 3.59/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.59/1.00    inference(nnf_transformation,[],[f21])).
% 3.59/1.00  
% 3.59/1.00  fof(f33,plain,(
% 3.59/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.59/1.00    inference(rectify,[],[f32])).
% 3.59/1.00  
% 3.59/1.00  fof(f34,plain,(
% 3.59/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f35,plain,(
% 3.59/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.59/1.00  
% 3.59/1.00  fof(f51,plain,(
% 3.59/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f35])).
% 3.59/1.00  
% 3.59/1.00  fof(f52,plain,(
% 3.59/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f35])).
% 3.59/1.00  
% 3.59/1.00  fof(f13,axiom,(
% 3.59/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f41,plain,(
% 3.59/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.59/1.00    inference(nnf_transformation,[],[f13])).
% 3.59/1.00  
% 3.59/1.00  fof(f42,plain,(
% 3.59/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.59/1.00    inference(rectify,[],[f41])).
% 3.59/1.00  
% 3.59/1.00  fof(f43,plain,(
% 3.59/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f44,plain,(
% 3.59/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 3.59/1.00  
% 3.59/1.00  fof(f69,plain,(
% 3.59/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.59/1.00    inference(cnf_transformation,[],[f44])).
% 3.59/1.00  
% 3.59/1.00  fof(f92,plain,(
% 3.59/1.00    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.59/1.00    inference(equality_resolution,[],[f69])).
% 3.59/1.00  
% 3.59/1.00  fof(f1,axiom,(
% 3.59/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f28,plain,(
% 3.59/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.59/1.00    inference(nnf_transformation,[],[f1])).
% 3.59/1.00  
% 3.59/1.00  fof(f29,plain,(
% 3.59/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.59/1.00    inference(rectify,[],[f28])).
% 3.59/1.00  
% 3.59/1.00  fof(f30,plain,(
% 3.59/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f31,plain,(
% 3.59/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.59/1.00  
% 3.59/1.00  fof(f48,plain,(
% 3.59/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f31])).
% 3.59/1.00  
% 3.59/1.00  fof(f8,axiom,(
% 3.59/1.00    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f63,plain,(
% 3.59/1.00    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 3.59/1.00    inference(cnf_transformation,[],[f8])).
% 3.59/1.00  
% 3.59/1.00  fof(f54,plain,(
% 3.59/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.59/1.00    inference(cnf_transformation,[],[f40])).
% 3.59/1.00  
% 3.59/1.00  fof(f90,plain,(
% 3.59/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.59/1.00    inference(equality_resolution,[],[f54])).
% 3.59/1.00  
% 3.59/1.00  fof(f19,conjecture,(
% 3.59/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f20,negated_conjecture,(
% 3.59/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 3.59/1.00    inference(negated_conjecture,[],[f19])).
% 3.59/1.00  
% 3.59/1.00  fof(f27,plain,(
% 3.59/1.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f20])).
% 3.59/1.00  
% 3.59/1.00  fof(f46,plain,(
% 3.59/1.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4)) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f47,plain,(
% 3.59/1.00    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4)) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f46])).
% 3.59/1.00  
% 3.59/1.00  fof(f80,plain,(
% 3.59/1.00    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 3.59/1.00    inference(cnf_transformation,[],[f47])).
% 3.59/1.00  
% 3.59/1.00  fof(f68,plain,(
% 3.59/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.59/1.00    inference(cnf_transformation,[],[f44])).
% 3.59/1.00  
% 3.59/1.00  fof(f93,plain,(
% 3.59/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.59/1.00    inference(equality_resolution,[],[f68])).
% 3.59/1.00  
% 3.59/1.00  fof(f5,axiom,(
% 3.59/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f22,plain,(
% 3.59/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.59/1.00    inference(ennf_transformation,[],[f5])).
% 3.59/1.00  
% 3.59/1.00  fof(f60,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f22])).
% 3.59/1.00  
% 3.59/1.00  fof(f7,axiom,(
% 3.59/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f62,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f7])).
% 3.59/1.00  
% 3.59/1.00  fof(f85,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.59/1.00    inference(definition_unfolding,[],[f60,f62])).
% 3.59/1.00  
% 3.59/1.00  fof(f53,plain,(
% 3.59/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.59/1.00    inference(cnf_transformation,[],[f40])).
% 3.59/1.00  
% 3.59/1.00  fof(f91,plain,(
% 3.59/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.59/1.00    inference(equality_resolution,[],[f53])).
% 3.59/1.00  
% 3.59/1.00  fof(f6,axiom,(
% 3.59/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f61,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.59/1.00    inference(cnf_transformation,[],[f6])).
% 3.59/1.00  
% 3.59/1.00  fof(f14,axiom,(
% 3.59/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f72,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.59/1.00    inference(cnf_transformation,[],[f14])).
% 3.59/1.00  
% 3.59/1.00  fof(f11,axiom,(
% 3.59/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f66,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f11])).
% 3.59/1.00  
% 3.59/1.00  fof(f12,axiom,(
% 3.59/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f67,plain,(
% 3.59/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f12])).
% 3.59/1.00  
% 3.59/1.00  fof(f82,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.59/1.00    inference(definition_unfolding,[],[f66,f67])).
% 3.59/1.00  
% 3.59/1.00  fof(f83,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.59/1.00    inference(definition_unfolding,[],[f72,f82])).
% 3.59/1.00  
% 3.59/1.00  fof(f86,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 3.59/1.00    inference(definition_unfolding,[],[f61,f83,f83])).
% 3.59/1.00  
% 3.59/1.00  fof(f18,axiom,(
% 3.59/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f25,plain,(
% 3.59/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.59/1.00    inference(ennf_transformation,[],[f18])).
% 3.59/1.00  
% 3.59/1.00  fof(f26,plain,(
% 3.59/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.59/1.00    inference(flattening,[],[f25])).
% 3.59/1.00  
% 3.59/1.00  fof(f79,plain,(
% 3.59/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.59/1.00    inference(cnf_transformation,[],[f26])).
% 3.59/1.00  
% 3.59/1.00  fof(f88,plain,(
% 3.59/1.00    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.59/1.00    inference(definition_unfolding,[],[f79,f83])).
% 3.59/1.00  
% 3.59/1.00  fof(f4,axiom,(
% 3.59/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f59,plain,(
% 3.59/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.59/1.00    inference(cnf_transformation,[],[f4])).
% 3.59/1.00  
% 3.59/1.00  fof(f84,plain,(
% 3.59/1.00    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.59/1.00    inference(definition_unfolding,[],[f59,f83])).
% 3.59/1.00  
% 3.59/1.00  fof(f10,axiom,(
% 3.59/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f65,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f10])).
% 3.59/1.00  
% 3.59/1.00  fof(f87,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.59/1.00    inference(definition_unfolding,[],[f65,f82,f82])).
% 3.59/1.00  
% 3.59/1.00  fof(f81,plain,(
% 3.59/1.00    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4))),
% 3.59/1.00    inference(cnf_transformation,[],[f47])).
% 3.59/1.00  
% 3.59/1.00  cnf(c_7,plain,
% 3.59/1.00      ( r2_hidden(sK2(X0,X1,X2),X0)
% 3.59/1.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.59/1.00      | k4_xboole_0(X0,X1) = X2 ),
% 3.59/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_840,plain,
% 3.59/1.00      ( k4_xboole_0(X0,X1) = X2
% 3.59/1.00      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 3.59/1.00      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_26,plain,
% 3.59/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_827,plain,
% 3.59/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_25,plain,
% 3.59/1.00      ( k2_subset_1(X0) = X0 ),
% 3.59/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_854,plain,
% 3.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.59/1.00      inference(light_normalisation,[status(thm)],[c_827,c_25]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_24,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_828,plain,
% 3.59/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.59/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.59/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1655,plain,
% 3.59/1.00      ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top
% 3.59/1.00      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_854,c_828]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3,plain,
% 3.59/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_844,plain,
% 3.59/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.59/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2,plain,
% 3.59/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_845,plain,
% 3.59/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.59/1.00      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2155,plain,
% 3.59/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_844,c_845]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_19,plain,
% 3.59/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_832,plain,
% 3.59/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.59/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1,plain,
% 3.59/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_846,plain,
% 3.59/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.59/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1635,plain,
% 3.59/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.59/1.00      | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_832,c_846]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5130,plain,
% 3.59/1.00      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2155,c_1635]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6376,plain,
% 3.59/1.00      ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_1655,c_5130]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_14,plain,
% 3.59/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.59/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9,plain,
% 3.59/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_838,plain,
% 3.59/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.59/1.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2430,plain,
% 3.59/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.59/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_14,c_838]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6383,plain,
% 3.59/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_6376,c_2430]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6396,plain,
% 3.59/1.00      ( k4_xboole_0(k1_xboole_0,X0) = X1
% 3.59/1.00      | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_840,c_6383]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6409,plain,
% 3.59/1.00      ( k1_xboole_0 = X0
% 3.59/1.00      | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.59/1.00      inference(demodulation,[status(thm)],[c_6396,c_14]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_29,negated_conjecture,
% 3.59/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_825,plain,
% 3.59/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1654,plain,
% 3.59/1.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
% 3.59/1.00      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_825,c_828]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1134,plain,
% 3.59/1.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) | v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 3.59/1.00      inference(resolution,[status(thm)],[c_24,c_29]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_52,plain,
% 3.59/1.00      ( ~ r1_tarski(sK4,sK4) | r2_hidden(sK4,k1_zfmisc_1(sK4)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_84,plain,
% 3.59/1.00      ( r1_tarski(sK4,sK4) | r2_hidden(sK1(sK4,sK4),sK4) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_87,plain,
% 3.59/1.00      ( r1_tarski(sK4,sK4) | ~ r2_hidden(sK1(sK4,sK4),sK4) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1079,plain,
% 3.59/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.59/1.00      | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1081,plain,
% 3.59/1.00      ( ~ r2_hidden(sK4,k1_zfmisc_1(sK4))
% 3.59/1.00      | ~ v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_1079]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1137,plain,
% 3.59/1.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_1134,c_52,c_84,c_87,c_1081]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1139,plain,
% 3.59/1.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5859,plain,
% 3.59/1.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_1654,c_1139]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_20,plain,
% 3.59/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_831,plain,
% 3.59/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.59/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5867,plain,
% 3.59/1.00      ( r1_tarski(sK5,sK4) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_5859,c_831]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_12,plain,
% 3.59/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.59/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_836,plain,
% 3.59/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.59/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6144,plain,
% 3.59/1.00      ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) = sK5 ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_5867,c_836]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_7355,plain,
% 3.59/1.00      ( r2_hidden(X0,k4_xboole_0(sK5,sK4)) != iProver_top
% 3.59/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_6144,c_838]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_10,plain,
% 3.59/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_837,plain,
% 3.59/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.59/1.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_10281,plain,
% 3.59/1.00      ( r2_hidden(X0,k4_xboole_0(sK5,sK4)) != iProver_top ),
% 3.59/1.00      inference(forward_subsumption_resolution,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_7355,c_837]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_10293,plain,
% 3.59/1.00      ( k4_xboole_0(sK5,sK4) = k1_xboole_0 ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_6409,c_10281]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_13,plain,
% 3.59/1.00      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_10655,plain,
% 3.59/1.00      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = k3_tarski(k2_enumset1(sK4,sK4,sK4,k1_xboole_0)) ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_10293,c_13]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_27,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.59/1.00      | k3_tarski(k2_enumset1(X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_826,plain,
% 3.59/1.00      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.59/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.59/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1269,plain,
% 3.59/1.00      ( k3_tarski(k2_enumset1(X0,X0,X0,sK5)) = k4_subset_1(sK4,X0,sK5)
% 3.59/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_825,c_826]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3806,plain,
% 3.59/1.00      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = k4_subset_1(sK4,sK4,sK5) ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_854,c_1269]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_10657,plain,
% 3.59/1.00      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,k1_xboole_0)) = k4_subset_1(sK4,sK4,sK5) ),
% 3.59/1.00      inference(light_normalisation,[status(thm)],[c_10655,c_3806]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_11,plain,
% 3.59/1.00      ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.59/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_10658,plain,
% 3.59/1.00      ( k4_subset_1(sK4,sK4,sK5) = sK4 ),
% 3.59/1.00      inference(demodulation,[status(thm)],[c_10657,c_11]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_16,plain,
% 3.59/1.00      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1270,plain,
% 3.59/1.00      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X1,X0,X1)
% 3.59/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_854,c_826]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4126,plain,
% 3.59/1.00      ( k3_tarski(k2_enumset1(sK5,sK5,sK5,sK4)) = k4_subset_1(sK4,sK5,sK4) ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_825,c_1270]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5137,plain,
% 3.59/1.00      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = k4_subset_1(sK4,sK5,sK4) ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_16,c_4126]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5140,plain,
% 3.59/1.00      ( k4_subset_1(sK4,sK4,sK5) = k4_subset_1(sK4,sK5,sK4) ),
% 3.59/1.00      inference(light_normalisation,[status(thm)],[c_5137,c_3806]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_28,negated_conjecture,
% 3.59/1.00      ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_859,plain,
% 3.59/1.00      ( k4_subset_1(sK4,sK5,sK4) != sK4 ),
% 3.59/1.00      inference(demodulation,[status(thm)],[c_28,c_25]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5248,plain,
% 3.59/1.00      ( k4_subset_1(sK4,sK4,sK5) != sK4 ),
% 3.59/1.00      inference(demodulation,[status(thm)],[c_5140,c_859]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(contradiction,plain,
% 3.59/1.00      ( $false ),
% 3.59/1.00      inference(minisat,[status(thm)],[c_10658,c_5248]) ).
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  ------                               Statistics
% 3.59/1.00  
% 3.59/1.00  ------ Selected
% 3.59/1.00  
% 3.59/1.00  total_time:                             0.355
% 3.59/1.00  
%------------------------------------------------------------------------------
