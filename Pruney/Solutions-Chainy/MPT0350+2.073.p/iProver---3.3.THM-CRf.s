%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:16 EST 2020

% Result     : Theorem 43.33s
% Output     : CNFRefutation 43.33s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 266 expanded)
%              Number of clauses        :   67 ( 101 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  396 ( 776 expanded)
%              Number of equality atoms :  162 ( 274 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f39])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f53,f53])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f54,f71,f53])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_272,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_133281,plain,
    ( X0 != X1
    | X0 = k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
    | k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) != X1 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_133282,plain,
    ( k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) != sK3
    | sK3 = k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_133281])).

cnf(c_1133,plain,
    ( X0 != X1
    | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != X1
    | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_63786,plain,
    ( X0 != k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
    | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = X0
    | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_63787,plain,
    ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
    | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = sK3
    | sK3 != k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_63786])).

cnf(c_3752,plain,
    ( X0 != k4_subset_1(X1,sK4,k4_xboole_0(sK3,sK4))
    | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = X0
    | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != k4_subset_1(X1,sK4,k4_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_50340,plain,
    ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != k4_subset_1(X0,sK4,k4_xboole_0(sK3,sK4))
    | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
    | k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) != k4_subset_1(X0,sK4,k4_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3752])).

cnf(c_50342,plain,
    ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != k4_subset_1(sK3,sK4,k4_xboole_0(sK3,sK4))
    | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
    | k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) != k4_subset_1(sK3,sK4,k4_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_50340])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_810,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_790,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_794,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1989,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_794])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1005,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
    | r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1006,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_2401,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1989,c_27,c_33,c_1006])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_798,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2406,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2401,c_798])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_802,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2550,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_2406,c_802])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2566,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_2550,c_1])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_803,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3371,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2566,c_803])).

cnf(c_4493,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),X0),sK3) = iProver_top
    | r1_tarski(k4_xboole_0(sK3,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_810,c_3371])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_811,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_45732,plain,
    ( r1_tarski(k4_xboole_0(sK3,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4493,c_811])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_25792,plain,
    ( r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0))
    | ~ r1_tarski(k4_xboole_0(sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_25793,plain,
    ( r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k4_xboole_0(sK3,sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25792])).

cnf(c_25795,plain,
    ( r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(k4_xboole_0(sK3,sK4),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_25793])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k1_enumset1(X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_11062,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) = k4_subset_1(X0,sK4,k4_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_11064,plain,
    ( k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) = k4_subset_1(X0,sK4,k4_xboole_0(sK3,sK4))
    | m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11062])).

cnf(c_11066,plain,
    ( k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) = k4_subset_1(sK3,sK4,k4_xboole_0(sK3,sK4))
    | m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11064])).

cnf(c_19,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1000,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_10653,plain,
    ( m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0))
    | ~ r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0))
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_10654,plain,
    ( m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0)) = iProver_top
    | r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10653])).

cnf(c_10656,plain,
    ( m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10654])).

cnf(c_12,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2792,plain,
    ( k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) = sK3 ),
    inference(superposition,[status(thm)],[c_2566,c_12])).

cnf(c_284,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_1135,plain,
    ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k4_subset_1(X0,X1,X2)
    | k3_subset_1(sK3,sK4) != X2
    | sK4 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_1454,plain,
    ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k4_subset_1(X0,sK4,X1)
    | k3_subset_1(sK3,sK4) != X1
    | sK4 != sK4
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_2158,plain,
    ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k4_subset_1(X0,sK4,k4_xboole_0(sK3,sK4))
    | k3_subset_1(sK3,sK4) != k4_xboole_0(sK3,sK4)
    | sK4 != sK4
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_2159,plain,
    ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k4_subset_1(sK3,sK4,k4_xboole_0(sK3,sK4))
    | k3_subset_1(sK3,sK4) != k4_xboole_0(sK3,sK4)
    | sK4 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2158])).

cnf(c_271,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1186,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1008,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
    | k3_subset_1(sK3,sK4) = k4_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_25,negated_conjecture,
    ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_818,plain,
    ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != sK3 ),
    inference(demodulation,[status(thm)],[c_25,c_21])).

cnf(c_298,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_133282,c_63787,c_50342,c_45732,c_25795,c_11066,c_10656,c_2792,c_2159,c_1186,c_1008,c_818,c_298,c_33,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.33/5.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.33/5.99  
% 43.33/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.33/5.99  
% 43.33/5.99  ------  iProver source info
% 43.33/5.99  
% 43.33/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.33/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.33/5.99  git: non_committed_changes: false
% 43.33/5.99  git: last_make_outside_of_git: false
% 43.33/5.99  
% 43.33/5.99  ------ 
% 43.33/5.99  ------ Parsing...
% 43.33/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.33/5.99  
% 43.33/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 43.33/5.99  
% 43.33/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.33/5.99  
% 43.33/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.33/5.99  ------ Proving...
% 43.33/5.99  ------ Problem Properties 
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  clauses                                 27
% 43.33/5.99  conjectures                             2
% 43.33/5.99  EPR                                     5
% 43.33/5.99  Horn                                    21
% 43.33/5.99  unary                                   7
% 43.33/5.99  binary                                  8
% 43.33/5.99  lits                                    60
% 43.33/5.99  lits eq                                 13
% 43.33/5.99  fd_pure                                 0
% 43.33/5.99  fd_pseudo                               0
% 43.33/5.99  fd_cond                                 0
% 43.33/5.99  fd_pseudo_cond                          5
% 43.33/5.99  AC symbols                              0
% 43.33/5.99  
% 43.33/5.99  ------ Input Options Time Limit: Unbounded
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  ------ 
% 43.33/5.99  Current options:
% 43.33/5.99  ------ 
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  ------ Proving...
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  % SZS status Theorem for theBenchmark.p
% 43.33/5.99  
% 43.33/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 43.33/5.99  
% 43.33/5.99  fof(f2,axiom,(
% 43.33/5.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f18,plain,(
% 43.33/5.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 43.33/5.99    inference(ennf_transformation,[],[f2])).
% 43.33/5.99  
% 43.33/5.99  fof(f25,plain,(
% 43.33/5.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 43.33/5.99    inference(nnf_transformation,[],[f18])).
% 43.33/5.99  
% 43.33/5.99  fof(f26,plain,(
% 43.33/5.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 43.33/5.99    inference(rectify,[],[f25])).
% 43.33/5.99  
% 43.33/5.99  fof(f27,plain,(
% 43.33/5.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 43.33/5.99    introduced(choice_axiom,[])).
% 43.33/5.99  
% 43.33/5.99  fof(f28,plain,(
% 43.33/5.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 43.33/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 43.33/5.99  
% 43.33/5.99  fof(f43,plain,(
% 43.33/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f28])).
% 43.33/5.99  
% 43.33/5.99  fof(f16,conjecture,(
% 43.33/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f17,negated_conjecture,(
% 43.33/5.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 43.33/5.99    inference(negated_conjecture,[],[f16])).
% 43.33/5.99  
% 43.33/5.99  fof(f24,plain,(
% 43.33/5.99    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.33/5.99    inference(ennf_transformation,[],[f17])).
% 43.33/5.99  
% 43.33/5.99  fof(f39,plain,(
% 43.33/5.99    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 43.33/5.99    introduced(choice_axiom,[])).
% 43.33/5.99  
% 43.33/5.99  fof(f40,plain,(
% 43.33/5.99    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 43.33/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f39])).
% 43.33/5.99  
% 43.33/5.99  fof(f69,plain,(
% 43.33/5.99    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 43.33/5.99    inference(cnf_transformation,[],[f40])).
% 43.33/5.99  
% 43.33/5.99  fof(f11,axiom,(
% 43.33/5.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f20,plain,(
% 43.33/5.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 43.33/5.99    inference(ennf_transformation,[],[f11])).
% 43.33/5.99  
% 43.33/5.99  fof(f38,plain,(
% 43.33/5.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 43.33/5.99    inference(nnf_transformation,[],[f20])).
% 43.33/5.99  
% 43.33/5.99  fof(f61,plain,(
% 43.33/5.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f38])).
% 43.33/5.99  
% 43.33/5.99  fof(f14,axiom,(
% 43.33/5.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f67,plain,(
% 43.33/5.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 43.33/5.99    inference(cnf_transformation,[],[f14])).
% 43.33/5.99  
% 43.33/5.99  fof(f9,axiom,(
% 43.33/5.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f34,plain,(
% 43.33/5.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 43.33/5.99    inference(nnf_transformation,[],[f9])).
% 43.33/5.99  
% 43.33/5.99  fof(f35,plain,(
% 43.33/5.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 43.33/5.99    inference(rectify,[],[f34])).
% 43.33/5.99  
% 43.33/5.99  fof(f36,plain,(
% 43.33/5.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 43.33/5.99    introduced(choice_axiom,[])).
% 43.33/5.99  
% 43.33/5.99  fof(f37,plain,(
% 43.33/5.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 43.33/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 43.33/5.99  
% 43.33/5.99  fof(f56,plain,(
% 43.33/5.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 43.33/5.99    inference(cnf_transformation,[],[f37])).
% 43.33/5.99  
% 43.33/5.99  fof(f87,plain,(
% 43.33/5.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 43.33/5.99    inference(equality_resolution,[],[f56])).
% 43.33/5.99  
% 43.33/5.99  fof(f5,axiom,(
% 43.33/5.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f19,plain,(
% 43.33/5.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 43.33/5.99    inference(ennf_transformation,[],[f5])).
% 43.33/5.99  
% 43.33/5.99  fof(f52,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f19])).
% 43.33/5.99  
% 43.33/5.99  fof(f6,axiom,(
% 43.33/5.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f53,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.33/5.99    inference(cnf_transformation,[],[f6])).
% 43.33/5.99  
% 43.33/5.99  fof(f80,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 43.33/5.99    inference(definition_unfolding,[],[f52,f53])).
% 43.33/5.99  
% 43.33/5.99  fof(f1,axiom,(
% 43.33/5.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f41,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f1])).
% 43.33/5.99  
% 43.33/5.99  fof(f73,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 43.33/5.99    inference(definition_unfolding,[],[f41,f53,f53])).
% 43.33/5.99  
% 43.33/5.99  fof(f3,axiom,(
% 43.33/5.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f29,plain,(
% 43.33/5.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.33/5.99    inference(nnf_transformation,[],[f3])).
% 43.33/5.99  
% 43.33/5.99  fof(f30,plain,(
% 43.33/5.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.33/5.99    inference(flattening,[],[f29])).
% 43.33/5.99  
% 43.33/5.99  fof(f31,plain,(
% 43.33/5.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.33/5.99    inference(rectify,[],[f30])).
% 43.33/5.99  
% 43.33/5.99  fof(f32,plain,(
% 43.33/5.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 43.33/5.99    introduced(choice_axiom,[])).
% 43.33/5.99  
% 43.33/5.99  fof(f33,plain,(
% 43.33/5.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.33/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 43.33/5.99  
% 43.33/5.99  fof(f45,plain,(
% 43.33/5.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 43.33/5.99    inference(cnf_transformation,[],[f33])).
% 43.33/5.99  
% 43.33/5.99  fof(f79,plain,(
% 43.33/5.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 43.33/5.99    inference(definition_unfolding,[],[f45,f53])).
% 43.33/5.99  
% 43.33/5.99  fof(f85,plain,(
% 43.33/5.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 43.33/5.99    inference(equality_resolution,[],[f79])).
% 43.33/5.99  
% 43.33/5.99  fof(f44,plain,(
% 43.33/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f28])).
% 43.33/5.99  
% 43.33/5.99  fof(f57,plain,(
% 43.33/5.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 43.33/5.99    inference(cnf_transformation,[],[f37])).
% 43.33/5.99  
% 43.33/5.99  fof(f86,plain,(
% 43.33/5.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 43.33/5.99    inference(equality_resolution,[],[f57])).
% 43.33/5.99  
% 43.33/5.99  fof(f15,axiom,(
% 43.33/5.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f22,plain,(
% 43.33/5.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 43.33/5.99    inference(ennf_transformation,[],[f15])).
% 43.33/5.99  
% 43.33/5.99  fof(f23,plain,(
% 43.33/5.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.33/5.99    inference(flattening,[],[f22])).
% 43.33/5.99  
% 43.33/5.99  fof(f68,plain,(
% 43.33/5.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.33/5.99    inference(cnf_transformation,[],[f23])).
% 43.33/5.99  
% 43.33/5.99  fof(f10,axiom,(
% 43.33/5.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f60,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 43.33/5.99    inference(cnf_transformation,[],[f10])).
% 43.33/5.99  
% 43.33/5.99  fof(f8,axiom,(
% 43.33/5.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f55,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f8])).
% 43.33/5.99  
% 43.33/5.99  fof(f71,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 43.33/5.99    inference(definition_unfolding,[],[f60,f55])).
% 43.33/5.99  
% 43.33/5.99  fof(f82,plain,(
% 43.33/5.99    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.33/5.99    inference(definition_unfolding,[],[f68,f71])).
% 43.33/5.99  
% 43.33/5.99  fof(f62,plain,(
% 43.33/5.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f38])).
% 43.33/5.99  
% 43.33/5.99  fof(f7,axiom,(
% 43.33/5.99    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f54,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 43.33/5.99    inference(cnf_transformation,[],[f7])).
% 43.33/5.99  
% 43.33/5.99  fof(f81,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 43.33/5.99    inference(definition_unfolding,[],[f54,f71,f53])).
% 43.33/5.99  
% 43.33/5.99  fof(f13,axiom,(
% 43.33/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f21,plain,(
% 43.33/5.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.33/5.99    inference(ennf_transformation,[],[f13])).
% 43.33/5.99  
% 43.33/5.99  fof(f66,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.33/5.99    inference(cnf_transformation,[],[f21])).
% 43.33/5.99  
% 43.33/5.99  fof(f70,plain,(
% 43.33/5.99    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4))),
% 43.33/5.99    inference(cnf_transformation,[],[f40])).
% 43.33/5.99  
% 43.33/5.99  fof(f12,axiom,(
% 43.33/5.99    ! [X0] : k2_subset_1(X0) = X0),
% 43.33/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f65,plain,(
% 43.33/5.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 43.33/5.99    inference(cnf_transformation,[],[f12])).
% 43.33/5.99  
% 43.33/5.99  cnf(c_272,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_133281,plain,
% 43.33/5.99      ( X0 != X1
% 43.33/5.99      | X0 = k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
% 43.33/5.99      | k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) != X1 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_272]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_133282,plain,
% 43.33/5.99      ( k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) != sK3
% 43.33/5.99      | sK3 = k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
% 43.33/5.99      | sK3 != sK3 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_133281]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1133,plain,
% 43.33/5.99      ( X0 != X1
% 43.33/5.99      | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != X1
% 43.33/5.99      | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = X0 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_272]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_63786,plain,
% 43.33/5.99      ( X0 != k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
% 43.33/5.99      | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = X0
% 43.33/5.99      | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1133]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_63787,plain,
% 43.33/5.99      ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
% 43.33/5.99      | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = sK3
% 43.33/5.99      | sK3 != k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_63786]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_3752,plain,
% 43.33/5.99      ( X0 != k4_subset_1(X1,sK4,k4_xboole_0(sK3,sK4))
% 43.33/5.99      | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = X0
% 43.33/5.99      | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != k4_subset_1(X1,sK4,k4_xboole_0(sK3,sK4)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1133]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_50340,plain,
% 43.33/5.99      ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != k4_subset_1(X0,sK4,k4_xboole_0(sK3,sK4))
% 43.33/5.99      | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
% 43.33/5.99      | k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) != k4_subset_1(X0,sK4,k4_xboole_0(sK3,sK4)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_3752]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_50342,plain,
% 43.33/5.99      ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != k4_subset_1(sK3,sK4,k4_xboole_0(sK3,sK4))
% 43.33/5.99      | k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4)))
% 43.33/5.99      | k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) != k4_subset_1(sK3,sK4,k4_xboole_0(sK3,sK4)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_50340]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_3,plain,
% 43.33/5.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f43]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_810,plain,
% 43.33/5.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 43.33/5.99      | r1_tarski(X0,X1) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_26,negated_conjecture,
% 43.33/5.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 43.33/5.99      inference(cnf_transformation,[],[f69]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_790,plain,
% 43.33/5.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_20,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f61]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_794,plain,
% 43.33/5.99      ( m1_subset_1(X0,X1) != iProver_top
% 43.33/5.99      | r2_hidden(X0,X1) = iProver_top
% 43.33/5.99      | v1_xboole_0(X1) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1989,plain,
% 43.33/5.99      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
% 43.33/5.99      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 43.33/5.99      inference(superposition,[status(thm)],[c_790,c_794]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_27,plain,
% 43.33/5.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_23,plain,
% 43.33/5.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 43.33/5.99      inference(cnf_transformation,[],[f67]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_31,plain,
% 43.33/5.99      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_33,plain,
% 43.33/5.99      ( v1_xboole_0(k1_zfmisc_1(sK3)) != iProver_top ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_31]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1005,plain,
% 43.33/5.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
% 43.33/5.99      | r2_hidden(sK4,k1_zfmisc_1(sK3))
% 43.33/5.99      | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_20]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1006,plain,
% 43.33/5.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top
% 43.33/5.99      | r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
% 43.33/5.99      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_1005]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2401,plain,
% 43.33/5.99      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 43.33/5.99      inference(global_propositional_subsumption,
% 43.33/5.99                [status(thm)],
% 43.33/5.99                [c_1989,c_27,c_33,c_1006]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_16,plain,
% 43.33/5.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f87]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_798,plain,
% 43.33/5.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 43.33/5.99      | r1_tarski(X0,X1) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2406,plain,
% 43.33/5.99      ( r1_tarski(sK4,sK3) = iProver_top ),
% 43.33/5.99      inference(superposition,[status(thm)],[c_2401,c_798]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_11,plain,
% 43.33/5.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 43.33/5.99      inference(cnf_transformation,[],[f80]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_802,plain,
% 43.33/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 43.33/5.99      | r1_tarski(X0,X1) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2550,plain,
% 43.33/5.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = sK4 ),
% 43.33/5.99      inference(superposition,[status(thm)],[c_2406,c_802]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1,plain,
% 43.33/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 43.33/5.99      inference(cnf_transformation,[],[f73]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2566,plain,
% 43.33/5.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = sK4 ),
% 43.33/5.99      inference(superposition,[status(thm)],[c_2550,c_1]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_10,plain,
% 43.33/5.99      ( r2_hidden(X0,X1)
% 43.33/5.99      | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 43.33/5.99      inference(cnf_transformation,[],[f85]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_803,plain,
% 43.33/5.99      ( r2_hidden(X0,X1) = iProver_top
% 43.33/5.99      | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_3371,plain,
% 43.33/5.99      ( r2_hidden(X0,k4_xboole_0(sK3,sK4)) != iProver_top
% 43.33/5.99      | r2_hidden(X0,sK3) = iProver_top ),
% 43.33/5.99      inference(superposition,[status(thm)],[c_2566,c_803]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_4493,plain,
% 43.33/5.99      ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),X0),sK3) = iProver_top
% 43.33/5.99      | r1_tarski(k4_xboole_0(sK3,sK4),X0) = iProver_top ),
% 43.33/5.99      inference(superposition,[status(thm)],[c_810,c_3371]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2,plain,
% 43.33/5.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f44]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_811,plain,
% 43.33/5.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 43.33/5.99      | r1_tarski(X0,X1) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_45732,plain,
% 43.33/5.99      ( r1_tarski(k4_xboole_0(sK3,sK4),sK3) = iProver_top ),
% 43.33/5.99      inference(superposition,[status(thm)],[c_4493,c_811]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_15,plain,
% 43.33/5.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f86]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_25792,plain,
% 43.33/5.99      ( r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0))
% 43.33/5.99      | ~ r1_tarski(k4_xboole_0(sK3,sK4),X0) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_15]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_25793,plain,
% 43.33/5.99      ( r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0)) = iProver_top
% 43.33/5.99      | r1_tarski(k4_xboole_0(sK3,sK4),X0) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_25792]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_25795,plain,
% 43.33/5.99      ( r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
% 43.33/5.99      | r1_tarski(k4_xboole_0(sK3,sK4),sK3) != iProver_top ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_25793]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_24,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.33/5.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 43.33/5.99      | k3_tarski(k1_enumset1(X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 43.33/5.99      inference(cnf_transformation,[],[f82]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_11062,plain,
% 43.33/5.99      ( ~ m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0))
% 43.33/5.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 43.33/5.99      | k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) = k4_subset_1(X0,sK4,k4_xboole_0(sK3,sK4)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_24]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_11064,plain,
% 43.33/5.99      ( k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) = k4_subset_1(X0,sK4,k4_xboole_0(sK3,sK4))
% 43.33/5.99      | m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0)) != iProver_top
% 43.33/5.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_11062]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_11066,plain,
% 43.33/5.99      ( k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) = k4_subset_1(sK3,sK4,k4_xboole_0(sK3,sK4))
% 43.33/5.99      | m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
% 43.33/5.99      | m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_11064]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_19,plain,
% 43.33/5.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f62]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1000,plain,
% 43.33/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.33/5.99      | ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 43.33/5.99      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_19]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_10653,plain,
% 43.33/5.99      ( m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0))
% 43.33/5.99      | ~ r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0))
% 43.33/5.99      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1000]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_10654,plain,
% 43.33/5.99      ( m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0)) = iProver_top
% 43.33/5.99      | r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(X0)) != iProver_top
% 43.33/5.99      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_10653]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_10656,plain,
% 43.33/5.99      ( m1_subset_1(k4_xboole_0(sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
% 43.33/5.99      | r2_hidden(k4_xboole_0(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
% 43.33/5.99      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_10654]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_12,plain,
% 43.33/5.99      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
% 43.33/5.99      inference(cnf_transformation,[],[f81]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2792,plain,
% 43.33/5.99      ( k3_tarski(k1_enumset1(sK4,sK4,k4_xboole_0(sK3,sK4))) = sK3 ),
% 43.33/5.99      inference(superposition,[status(thm)],[c_2566,c_12]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_284,plain,
% 43.33/5.99      ( X0 != X1
% 43.33/5.99      | X2 != X3
% 43.33/5.99      | X4 != X5
% 43.33/5.99      | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
% 43.33/5.99      theory(equality) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1135,plain,
% 43.33/5.99      ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k4_subset_1(X0,X1,X2)
% 43.33/5.99      | k3_subset_1(sK3,sK4) != X2
% 43.33/5.99      | sK4 != X1
% 43.33/5.99      | sK3 != X0 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_284]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1454,plain,
% 43.33/5.99      ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k4_subset_1(X0,sK4,X1)
% 43.33/5.99      | k3_subset_1(sK3,sK4) != X1
% 43.33/5.99      | sK4 != sK4
% 43.33/5.99      | sK3 != X0 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1135]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2158,plain,
% 43.33/5.99      ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k4_subset_1(X0,sK4,k4_xboole_0(sK3,sK4))
% 43.33/5.99      | k3_subset_1(sK3,sK4) != k4_xboole_0(sK3,sK4)
% 43.33/5.99      | sK4 != sK4
% 43.33/5.99      | sK3 != X0 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1454]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2159,plain,
% 43.33/5.99      ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) = k4_subset_1(sK3,sK4,k4_xboole_0(sK3,sK4))
% 43.33/5.99      | k3_subset_1(sK3,sK4) != k4_xboole_0(sK3,sK4)
% 43.33/5.99      | sK4 != sK4
% 43.33/5.99      | sK3 != sK3 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_2158]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_271,plain,( X0 = X0 ),theory(equality) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1186,plain,
% 43.33/5.99      ( sK4 = sK4 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_271]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_22,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.33/5.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 43.33/5.99      inference(cnf_transformation,[],[f66]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1008,plain,
% 43.33/5.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
% 43.33/5.99      | k3_subset_1(sK3,sK4) = k4_xboole_0(sK3,sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_22]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_25,negated_conjecture,
% 43.33/5.99      ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) ),
% 43.33/5.99      inference(cnf_transformation,[],[f70]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_21,plain,
% 43.33/5.99      ( k2_subset_1(X0) = X0 ),
% 43.33/5.99      inference(cnf_transformation,[],[f65]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_818,plain,
% 43.33/5.99      ( k4_subset_1(sK3,sK4,k3_subset_1(sK3,sK4)) != sK3 ),
% 43.33/5.99      inference(demodulation,[status(thm)],[c_25,c_21]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_298,plain,
% 43.33/5.99      ( sK3 = sK3 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_271]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(contradiction,plain,
% 43.33/5.99      ( $false ),
% 43.33/5.99      inference(minisat,
% 43.33/5.99                [status(thm)],
% 43.33/5.99                [c_133282,c_63787,c_50342,c_45732,c_25795,c_11066,
% 43.33/5.99                 c_10656,c_2792,c_2159,c_1186,c_1008,c_818,c_298,c_33,
% 43.33/5.99                 c_27,c_26]) ).
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  % SZS output end CNFRefutation for theBenchmark.p
% 43.33/5.99  
% 43.33/5.99  ------                               Statistics
% 43.33/6.00  
% 43.33/6.00  ------ Selected
% 43.33/6.00  
% 43.33/6.00  total_time:                             5.013
% 43.33/6.00  
%------------------------------------------------------------------------------
