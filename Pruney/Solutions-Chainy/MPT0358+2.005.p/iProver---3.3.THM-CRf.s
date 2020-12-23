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
% DateTime   : Thu Dec  3 11:39:48 EST 2020

% Result     : Theorem 23.31s
% Output     : CNFRefutation 23.31s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 441 expanded)
%              Number of clauses        :   77 ( 157 expanded)
%              Number of leaves         :   25 (  94 expanded)
%              Depth                    :   20
%              Number of atoms          :  468 (1379 expanded)
%              Number of equality atoms :  152 ( 481 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f53,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f54,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f53])).

fof(f55,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK4) != sK5
        | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
      & ( k1_subset_1(sK4) = sK5
        | r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( k1_subset_1(sK4) != sK5
      | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
    & ( k1_subset_1(sK4) = sK5
      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f54,f55])).

fof(f96,plain,
    ( k1_subset_1(sK4) = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f56])).

fof(f20,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f109,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(definition_unfolding,[],[f96,f92])).

fof(f97,plain,
    ( k1_subset_1(sK4) != sK5
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f56])).

fof(f108,plain,
    ( k1_xboole_0 != sK5
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(definition_unfolding,[],[f97,f92])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f114,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f22,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f72,f81])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f93,f98])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f3])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f61,f98])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) ) ),
    inference(equality_resolution,[],[f104])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_848,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_846,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8615,plain,
    ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X3,k3_subset_1(X4,X5))
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution,[status(thm)],[c_848,c_846])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_73038,plain,
    ( r1_tarski(X0,k3_subset_1(X1,X2))
    | X1 != sK4
    | X0 != sK5
    | X2 != sK5
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_8615,c_36])).

cnf(c_35,negated_conjecture,
    ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_40,plain,
    ( k1_xboole_0 != sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_14,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1542,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1529,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1540,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14738,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(k3_subset_1(sK4,sK5),X0) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_1540])).

cnf(c_1906,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k3_subset_1(sK4,sK5) != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_2188,plain,
    ( ~ r1_tarski(X0,k3_subset_1(sK4,sK5))
    | r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k3_subset_1(sK4,sK5) != k3_subset_1(sK4,sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_2190,plain,
    ( k3_subset_1(sK4,sK5) != k3_subset_1(sK4,sK5)
    | sK5 != X0
    | r1_tarski(X0,k3_subset_1(sK4,sK5)) != iProver_top
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2188])).

cnf(c_2192,plain,
    ( k3_subset_1(sK4,sK5) != k3_subset_1(sK4,sK5)
    | sK5 != k1_xboole_0
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(sK4,sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_840,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2189,plain,
    ( k3_subset_1(sK4,sK5) = k3_subset_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_18,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2245,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2248,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2245])).

cnf(c_1942,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK5,X0)
    | r1_tarski(sK5,X1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_5225,plain,
    ( ~ r1_tarski(k3_subset_1(sK4,sK5),X0)
    | r1_tarski(sK5,X0)
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1942])).

cnf(c_5226,plain,
    ( r1_tarski(k3_subset_1(sK4,sK5),X0) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5225])).

cnf(c_15587,plain,
    ( r1_tarski(k3_subset_1(sK4,sK5),X0) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14738,c_2192,c_2189,c_2248,c_5226])).

cnf(c_15595,plain,
    ( r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_15587])).

cnf(c_73099,plain,
    ( X2 != sK5
    | X0 != sK5
    | X1 != sK4
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_73038,c_40,c_15595])).

cnf(c_73100,plain,
    ( r1_tarski(X0,k3_subset_1(X1,X2))
    | X1 != sK4
    | X0 != sK5
    | X2 != sK5 ),
    inference(renaming,[status(thm)],[c_73099])).

cnf(c_73135,plain,
    ( sK4 != sK4
    | sK5 != sK5
    | k1_xboole_0 != sK5 ),
    inference(resolution,[status(thm)],[c_73100,c_35])).

cnf(c_73136,plain,
    ( k1_xboole_0 != sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_73135])).

cnf(c_2855,plain,
    ( r1_tarski(X0,k3_subset_1(sK4,sK5))
    | ~ r1_tarski(X0,sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_16,c_36])).

cnf(c_2871,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_subset_1(sK4,sK5))
    | ~ r1_tarski(X1,sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_2855,c_16])).

cnf(c_27,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3038,plain,
    ( r1_tarski(X0,k3_subset_1(sK4,sK5))
    | ~ r1_tarski(X0,k1_tarski(X1))
    | ~ r2_hidden(X1,sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_2871,c_27])).

cnf(c_26,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2028,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(X0)),X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(resolution,[status(thm)],[c_26,c_1])).

cnf(c_34,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2225,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2028,c_34])).

cnf(c_3603,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(k1_tarski(X0))),k3_subset_1(sK4,sK5))
    | ~ r2_hidden(X0,sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_3038,c_2225])).

cnf(c_73875,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(k1_tarski(X0))),k3_subset_1(sK4,sK5))
    | ~ r2_hidden(X0,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_73136,c_3603])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_482,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_37])).

cnf(c_483,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,sK5),k2_xboole_0(X0,sK5))) = k3_subset_1(X0,sK5)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_1775,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))) = k3_subset_1(sK4,sK5) ),
    inference(equality_resolution,[status(thm)],[c_483])).

cnf(c_2515,plain,
    ( k1_tarski(X0) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_1901,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tarski(X2),X3)
    | X3 != X1
    | k1_tarski(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_2514,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r1_tarski(k1_tarski(X0),X2)
    | X2 != X1
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_5273,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r1_tarski(k1_tarski(X0),k3_subset_1(sK4,sK5))
    | X1 != k3_subset_1(sK4,sK5)
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_36982,plain,
    ( ~ r1_tarski(k1_tarski(X0),k3_subset_1(sK4,sK5))
    | r1_tarski(k1_tarski(X0),k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))))
    | k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))) != k3_subset_1(sK4,sK5)
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_5273])).

cnf(c_3593,plain,
    ( r1_tarski(k1_tarski(X0),k3_subset_1(sK4,sK5))
    | ~ r2_hidden(X0,sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_3038,c_14])).

cnf(c_73839,plain,
    ( r1_tarski(k1_tarski(X0),k3_subset_1(sK4,sK5))
    | ~ r2_hidden(X0,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_73136,c_3593])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_81016,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))))
    | ~ r2_hidden(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_28,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_87421,plain,
    ( ~ r1_tarski(k1_tarski(X0),k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))))
    | r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5)))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_88652,plain,
    ( ~ r2_hidden(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_73875,c_1775,c_2515,c_36982,c_73839,c_81016,c_87421])).

cnf(c_88724,plain,
    ( v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_88652,c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3623,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_20362,plain,
    ( ~ r2_hidden(sK2(X0,sK5),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3623])).

cnf(c_20364,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,sK5),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_20362])).

cnf(c_5240,plain,
    ( ~ r2_hidden(sK2(X0,sK5),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5247,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5240])).

cnf(c_841,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2783,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_2784,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2783])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1955,plain,
    ( r2_hidden(sK2(X0,sK5),X0)
    | r2_hidden(sK2(X0,sK5),sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1957,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK5),sK5)
    | r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0)
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1955])).

cnf(c_9,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_81,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_78,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88724,c_20364,c_15595,c_5247,c_2784,c_1957,c_9,c_81,c_78,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.31/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.31/3.49  
% 23.31/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.31/3.49  
% 23.31/3.49  ------  iProver source info
% 23.31/3.49  
% 23.31/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.31/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.31/3.49  git: non_committed_changes: false
% 23.31/3.49  git: last_make_outside_of_git: false
% 23.31/3.49  
% 23.31/3.49  ------ 
% 23.31/3.49  ------ Parsing...
% 23.31/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.31/3.49  
% 23.31/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.31/3.49  
% 23.31/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.31/3.49  
% 23.31/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.31/3.49  ------ Proving...
% 23.31/3.49  ------ Problem Properties 
% 23.31/3.49  
% 23.31/3.49  
% 23.31/3.49  clauses                                 34
% 23.31/3.49  conjectures                             2
% 23.31/3.49  EPR                                     7
% 23.31/3.49  Horn                                    26
% 23.31/3.49  unary                                   10
% 23.31/3.49  binary                                  14
% 23.31/3.49  lits                                    69
% 23.31/3.49  lits eq                                 20
% 23.31/3.49  fd_pure                                 0
% 23.31/3.49  fd_pseudo                               0
% 23.31/3.49  fd_cond                                 1
% 23.31/3.49  fd_pseudo_cond                          8
% 23.31/3.49  AC symbols                              0
% 23.31/3.49  
% 23.31/3.49  ------ Input Options Time Limit: Unbounded
% 23.31/3.49  
% 23.31/3.49  
% 23.31/3.49  ------ 
% 23.31/3.49  Current options:
% 23.31/3.49  ------ 
% 23.31/3.49  
% 23.31/3.49  
% 23.31/3.49  
% 23.31/3.49  
% 23.31/3.49  ------ Proving...
% 23.31/3.49  
% 23.31/3.49  
% 23.31/3.49  % SZS status Theorem for theBenchmark.p
% 23.31/3.49  
% 23.31/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.31/3.49  
% 23.31/3.49  fof(f23,conjecture,(
% 23.31/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f24,negated_conjecture,(
% 23.31/3.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 23.31/3.49    inference(negated_conjecture,[],[f23])).
% 23.31/3.49  
% 23.31/3.49  fof(f32,plain,(
% 23.31/3.49    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.31/3.49    inference(ennf_transformation,[],[f24])).
% 23.31/3.49  
% 23.31/3.49  fof(f53,plain,(
% 23.31/3.49    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.31/3.49    inference(nnf_transformation,[],[f32])).
% 23.31/3.49  
% 23.31/3.49  fof(f54,plain,(
% 23.31/3.49    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.31/3.49    inference(flattening,[],[f53])).
% 23.31/3.49  
% 23.31/3.49  fof(f55,plain,(
% 23.31/3.49    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))) & (k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 23.31/3.49    introduced(choice_axiom,[])).
% 23.31/3.49  
% 23.31/3.49  fof(f56,plain,(
% 23.31/3.49    (k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))) & (k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 23.31/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f54,f55])).
% 23.31/3.49  
% 23.31/3.49  fof(f96,plain,(
% 23.31/3.49    k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 23.31/3.49    inference(cnf_transformation,[],[f56])).
% 23.31/3.49  
% 23.31/3.49  fof(f20,axiom,(
% 23.31/3.49    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f92,plain,(
% 23.31/3.49    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 23.31/3.49    inference(cnf_transformation,[],[f20])).
% 23.31/3.49  
% 23.31/3.49  fof(f109,plain,(
% 23.31/3.49    k1_xboole_0 = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 23.31/3.49    inference(definition_unfolding,[],[f96,f92])).
% 23.31/3.49  
% 23.31/3.49  fof(f97,plain,(
% 23.31/3.49    k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 23.31/3.49    inference(cnf_transformation,[],[f56])).
% 23.31/3.49  
% 23.31/3.49  fof(f108,plain,(
% 23.31/3.49    k1_xboole_0 != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 23.31/3.49    inference(definition_unfolding,[],[f97,f92])).
% 23.31/3.49  
% 23.31/3.49  fof(f6,axiom,(
% 23.31/3.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f45,plain,(
% 23.31/3.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.31/3.49    inference(nnf_transformation,[],[f6])).
% 23.31/3.49  
% 23.31/3.49  fof(f46,plain,(
% 23.31/3.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.31/3.49    inference(flattening,[],[f45])).
% 23.31/3.49  
% 23.31/3.49  fof(f69,plain,(
% 23.31/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.31/3.49    inference(cnf_transformation,[],[f46])).
% 23.31/3.49  
% 23.31/3.49  fof(f114,plain,(
% 23.31/3.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.31/3.49    inference(equality_resolution,[],[f69])).
% 23.31/3.49  
% 23.31/3.49  fof(f9,axiom,(
% 23.31/3.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f27,plain,(
% 23.31/3.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 23.31/3.49    inference(ennf_transformation,[],[f9])).
% 23.31/3.49  
% 23.31/3.49  fof(f28,plain,(
% 23.31/3.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 23.31/3.49    inference(flattening,[],[f27])).
% 23.31/3.49  
% 23.31/3.49  fof(f74,plain,(
% 23.31/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 23.31/3.49    inference(cnf_transformation,[],[f28])).
% 23.31/3.49  
% 23.31/3.49  fof(f11,axiom,(
% 23.31/3.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f76,plain,(
% 23.31/3.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.31/3.49    inference(cnf_transformation,[],[f11])).
% 23.31/3.49  
% 23.31/3.49  fof(f18,axiom,(
% 23.31/3.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f51,plain,(
% 23.31/3.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 23.31/3.49    inference(nnf_transformation,[],[f18])).
% 23.31/3.49  
% 23.31/3.49  fof(f87,plain,(
% 23.31/3.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 23.31/3.49    inference(cnf_transformation,[],[f51])).
% 23.31/3.49  
% 23.31/3.49  fof(f17,axiom,(
% 23.31/3.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f47,plain,(
% 23.31/3.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.31/3.49    inference(nnf_transformation,[],[f17])).
% 23.31/3.49  
% 23.31/3.49  fof(f48,plain,(
% 23.31/3.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.31/3.49    inference(rectify,[],[f47])).
% 23.31/3.49  
% 23.31/3.49  fof(f49,plain,(
% 23.31/3.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 23.31/3.49    introduced(choice_axiom,[])).
% 23.31/3.49  
% 23.31/3.49  fof(f50,plain,(
% 23.31/3.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.31/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 23.31/3.49  
% 23.31/3.49  fof(f82,plain,(
% 23.31/3.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 23.31/3.49    inference(cnf_transformation,[],[f50])).
% 23.31/3.49  
% 23.31/3.49  fof(f116,plain,(
% 23.31/3.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 23.31/3.49    inference(equality_resolution,[],[f82])).
% 23.31/3.49  
% 23.31/3.49  fof(f2,axiom,(
% 23.31/3.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f33,plain,(
% 23.31/3.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 23.31/3.49    inference(nnf_transformation,[],[f2])).
% 23.31/3.49  
% 23.31/3.49  fof(f34,plain,(
% 23.31/3.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 23.31/3.49    inference(rectify,[],[f33])).
% 23.31/3.49  
% 23.31/3.49  fof(f35,plain,(
% 23.31/3.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 23.31/3.49    introduced(choice_axiom,[])).
% 23.31/3.49  
% 23.31/3.49  fof(f36,plain,(
% 23.31/3.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 23.31/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 23.31/3.49  
% 23.31/3.49  fof(f59,plain,(
% 23.31/3.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 23.31/3.49    inference(cnf_transformation,[],[f36])).
% 23.31/3.49  
% 23.31/3.49  fof(f22,axiom,(
% 23.31/3.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f94,plain,(
% 23.31/3.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 23.31/3.49    inference(cnf_transformation,[],[f22])).
% 23.31/3.49  
% 23.31/3.49  fof(f21,axiom,(
% 23.31/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f31,plain,(
% 23.31/3.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.31/3.49    inference(ennf_transformation,[],[f21])).
% 23.31/3.49  
% 23.31/3.49  fof(f93,plain,(
% 23.31/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.31/3.49    inference(cnf_transformation,[],[f31])).
% 23.31/3.49  
% 23.31/3.49  fof(f7,axiom,(
% 23.31/3.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f72,plain,(
% 23.31/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.31/3.49    inference(cnf_transformation,[],[f7])).
% 23.31/3.49  
% 23.31/3.49  fof(f16,axiom,(
% 23.31/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f81,plain,(
% 23.31/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 23.31/3.49    inference(cnf_transformation,[],[f16])).
% 23.31/3.49  
% 23.31/3.49  fof(f98,plain,(
% 23.31/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 23.31/3.49    inference(definition_unfolding,[],[f72,f81])).
% 23.31/3.49  
% 23.31/3.49  fof(f107,plain,(
% 23.31/3.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.31/3.49    inference(definition_unfolding,[],[f93,f98])).
% 23.31/3.49  
% 23.31/3.49  fof(f95,plain,(
% 23.31/3.49    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 23.31/3.49    inference(cnf_transformation,[],[f56])).
% 23.31/3.49  
% 23.31/3.49  fof(f3,axiom,(
% 23.31/3.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f37,plain,(
% 23.31/3.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.31/3.49    inference(nnf_transformation,[],[f3])).
% 23.31/3.49  
% 23.31/3.49  fof(f38,plain,(
% 23.31/3.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.31/3.49    inference(flattening,[],[f37])).
% 23.31/3.49  
% 23.31/3.49  fof(f39,plain,(
% 23.31/3.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.31/3.49    inference(rectify,[],[f38])).
% 23.31/3.49  
% 23.31/3.49  fof(f40,plain,(
% 23.31/3.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 23.31/3.49    introduced(choice_axiom,[])).
% 23.31/3.49  
% 23.31/3.49  fof(f41,plain,(
% 23.31/3.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.31/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 23.31/3.49  
% 23.31/3.49  fof(f61,plain,(
% 23.31/3.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 23.31/3.49    inference(cnf_transformation,[],[f41])).
% 23.31/3.49  
% 23.31/3.49  fof(f104,plain,(
% 23.31/3.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 23.31/3.49    inference(definition_unfolding,[],[f61,f98])).
% 23.31/3.49  
% 23.31/3.49  fof(f111,plain,(
% 23.31/3.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))) )),
% 23.31/3.49    inference(equality_resolution,[],[f104])).
% 23.31/3.49  
% 23.31/3.49  fof(f86,plain,(
% 23.31/3.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 23.31/3.49    inference(cnf_transformation,[],[f51])).
% 23.31/3.49  
% 23.31/3.49  fof(f58,plain,(
% 23.31/3.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 23.31/3.49    inference(cnf_transformation,[],[f36])).
% 23.31/3.49  
% 23.31/3.49  fof(f5,axiom,(
% 23.31/3.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f25,plain,(
% 23.31/3.49    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 23.31/3.49    inference(ennf_transformation,[],[f5])).
% 23.31/3.49  
% 23.31/3.49  fof(f42,plain,(
% 23.31/3.49    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 23.31/3.49    inference(nnf_transformation,[],[f25])).
% 23.31/3.49  
% 23.31/3.49  fof(f43,plain,(
% 23.31/3.49    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 23.31/3.49    introduced(choice_axiom,[])).
% 23.31/3.49  
% 23.31/3.49  fof(f44,plain,(
% 23.31/3.49    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 23.31/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 23.31/3.49  
% 23.31/3.49  fof(f67,plain,(
% 23.31/3.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 23.31/3.49    inference(cnf_transformation,[],[f44])).
% 23.31/3.49  
% 23.31/3.49  fof(f4,axiom,(
% 23.31/3.49    v1_xboole_0(k1_xboole_0)),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f66,plain,(
% 23.31/3.49    v1_xboole_0(k1_xboole_0)),
% 23.31/3.49    inference(cnf_transformation,[],[f4])).
% 23.31/3.49  
% 23.31/3.49  fof(f12,axiom,(
% 23.31/3.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 23.31/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.49  
% 23.31/3.49  fof(f29,plain,(
% 23.31/3.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 23.31/3.49    inference(ennf_transformation,[],[f12])).
% 23.31/3.49  
% 23.31/3.49  fof(f77,plain,(
% 23.31/3.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 23.31/3.49    inference(cnf_transformation,[],[f29])).
% 23.31/3.49  
% 23.31/3.49  cnf(c_848,plain,
% 23.31/3.49      ( X0 != X1 | X2 != X3 | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
% 23.31/3.49      theory(equality) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_846,plain,
% 23.31/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.31/3.49      theory(equality) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_8615,plain,
% 23.31/3.49      ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 23.31/3.49      | r1_tarski(X3,k3_subset_1(X4,X5))
% 23.31/3.49      | X3 != X0
% 23.31/3.49      | X4 != X1
% 23.31/3.49      | X5 != X2 ),
% 23.31/3.49      inference(resolution,[status(thm)],[c_848,c_846]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_36,negated_conjecture,
% 23.31/3.49      ( r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 = sK5 ),
% 23.31/3.49      inference(cnf_transformation,[],[f109]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_73038,plain,
% 23.31/3.49      ( r1_tarski(X0,k3_subset_1(X1,X2))
% 23.31/3.49      | X1 != sK4
% 23.31/3.49      | X0 != sK5
% 23.31/3.49      | X2 != sK5
% 23.31/3.49      | k1_xboole_0 = sK5 ),
% 23.31/3.49      inference(resolution,[status(thm)],[c_8615,c_36]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_35,negated_conjecture,
% 23.31/3.49      ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 != sK5 ),
% 23.31/3.49      inference(cnf_transformation,[],[f108]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_40,plain,
% 23.31/3.49      ( k1_xboole_0 != sK5
% 23.31/3.49      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) != iProver_top ),
% 23.31/3.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_14,plain,
% 23.31/3.49      ( r1_tarski(X0,X0) ),
% 23.31/3.49      inference(cnf_transformation,[],[f114]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_1542,plain,
% 23.31/3.49      ( r1_tarski(X0,X0) = iProver_top ),
% 23.31/3.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_1529,plain,
% 23.31/3.49      ( k1_xboole_0 = sK5
% 23.31/3.49      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
% 23.31/3.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_16,plain,
% 23.31/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 23.31/3.49      inference(cnf_transformation,[],[f74]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_1540,plain,
% 23.31/3.49      ( r1_tarski(X0,X1) != iProver_top
% 23.31/3.49      | r1_tarski(X1,X2) != iProver_top
% 23.31/3.49      | r1_tarski(X0,X2) = iProver_top ),
% 23.31/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_14738,plain,
% 23.31/3.49      ( sK5 = k1_xboole_0
% 23.31/3.49      | r1_tarski(k3_subset_1(sK4,sK5),X0) != iProver_top
% 23.31/3.49      | r1_tarski(sK5,X0) = iProver_top ),
% 23.31/3.49      inference(superposition,[status(thm)],[c_1529,c_1540]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_1906,plain,
% 23.31/3.49      ( ~ r1_tarski(X0,X1)
% 23.31/3.49      | r1_tarski(sK5,k3_subset_1(sK4,sK5))
% 23.31/3.49      | k3_subset_1(sK4,sK5) != X1
% 23.31/3.49      | sK5 != X0 ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_846]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2188,plain,
% 23.31/3.49      ( ~ r1_tarski(X0,k3_subset_1(sK4,sK5))
% 23.31/3.49      | r1_tarski(sK5,k3_subset_1(sK4,sK5))
% 23.31/3.49      | k3_subset_1(sK4,sK5) != k3_subset_1(sK4,sK5)
% 23.31/3.49      | sK5 != X0 ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_1906]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2190,plain,
% 23.31/3.49      ( k3_subset_1(sK4,sK5) != k3_subset_1(sK4,sK5)
% 23.31/3.49      | sK5 != X0
% 23.31/3.49      | r1_tarski(X0,k3_subset_1(sK4,sK5)) != iProver_top
% 23.31/3.49      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
% 23.31/3.49      inference(predicate_to_equality,[status(thm)],[c_2188]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2192,plain,
% 23.31/3.49      ( k3_subset_1(sK4,sK5) != k3_subset_1(sK4,sK5)
% 23.31/3.49      | sK5 != k1_xboole_0
% 23.31/3.49      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top
% 23.31/3.49      | r1_tarski(k1_xboole_0,k3_subset_1(sK4,sK5)) != iProver_top ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_2190]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_840,plain,( X0 = X0 ),theory(equality) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2189,plain,
% 23.31/3.49      ( k3_subset_1(sK4,sK5) = k3_subset_1(sK4,sK5) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_840]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_18,plain,
% 23.31/3.49      ( r1_tarski(k1_xboole_0,X0) ),
% 23.31/3.49      inference(cnf_transformation,[],[f76]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2245,plain,
% 23.31/3.49      ( r1_tarski(k1_xboole_0,k3_subset_1(sK4,sK5)) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_18]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2248,plain,
% 23.31/3.49      ( r1_tarski(k1_xboole_0,k3_subset_1(sK4,sK5)) = iProver_top ),
% 23.31/3.49      inference(predicate_to_equality,[status(thm)],[c_2245]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_1942,plain,
% 23.31/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(sK5,X0) | r1_tarski(sK5,X1) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_16]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_5225,plain,
% 23.31/3.49      ( ~ r1_tarski(k3_subset_1(sK4,sK5),X0)
% 23.31/3.49      | r1_tarski(sK5,X0)
% 23.31/3.49      | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_1942]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_5226,plain,
% 23.31/3.49      ( r1_tarski(k3_subset_1(sK4,sK5),X0) != iProver_top
% 23.31/3.49      | r1_tarski(sK5,X0) = iProver_top
% 23.31/3.49      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) != iProver_top ),
% 23.31/3.49      inference(predicate_to_equality,[status(thm)],[c_5225]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_15587,plain,
% 23.31/3.49      ( r1_tarski(k3_subset_1(sK4,sK5),X0) != iProver_top
% 23.31/3.49      | r1_tarski(sK5,X0) = iProver_top ),
% 23.31/3.49      inference(global_propositional_subsumption,
% 23.31/3.49                [status(thm)],
% 23.31/3.49                [c_14738,c_2192,c_2189,c_2248,c_5226]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_15595,plain,
% 23.31/3.49      ( r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
% 23.31/3.49      inference(superposition,[status(thm)],[c_1542,c_15587]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_73099,plain,
% 23.31/3.49      ( X2 != sK5
% 23.31/3.49      | X0 != sK5
% 23.31/3.49      | X1 != sK4
% 23.31/3.49      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 23.31/3.49      inference(global_propositional_subsumption,
% 23.31/3.49                [status(thm)],
% 23.31/3.49                [c_73038,c_40,c_15595]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_73100,plain,
% 23.31/3.49      ( r1_tarski(X0,k3_subset_1(X1,X2))
% 23.31/3.49      | X1 != sK4
% 23.31/3.49      | X0 != sK5
% 23.31/3.49      | X2 != sK5 ),
% 23.31/3.49      inference(renaming,[status(thm)],[c_73099]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_73135,plain,
% 23.31/3.49      ( sK4 != sK4 | sK5 != sK5 | k1_xboole_0 != sK5 ),
% 23.31/3.49      inference(resolution,[status(thm)],[c_73100,c_35]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_73136,plain,
% 23.31/3.49      ( k1_xboole_0 != sK5 ),
% 23.31/3.49      inference(equality_resolution_simp,[status(thm)],[c_73135]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2855,plain,
% 23.31/3.49      ( r1_tarski(X0,k3_subset_1(sK4,sK5))
% 23.31/3.49      | ~ r1_tarski(X0,sK5)
% 23.31/3.49      | k1_xboole_0 = sK5 ),
% 23.31/3.49      inference(resolution,[status(thm)],[c_16,c_36]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2871,plain,
% 23.31/3.49      ( ~ r1_tarski(X0,X1)
% 23.31/3.49      | r1_tarski(X0,k3_subset_1(sK4,sK5))
% 23.31/3.49      | ~ r1_tarski(X1,sK5)
% 23.31/3.49      | k1_xboole_0 = sK5 ),
% 23.31/3.49      inference(resolution,[status(thm)],[c_2855,c_16]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_27,plain,
% 23.31/3.49      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 23.31/3.49      inference(cnf_transformation,[],[f87]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_3038,plain,
% 23.31/3.49      ( r1_tarski(X0,k3_subset_1(sK4,sK5))
% 23.31/3.49      | ~ r1_tarski(X0,k1_tarski(X1))
% 23.31/3.49      | ~ r2_hidden(X1,sK5)
% 23.31/3.49      | k1_xboole_0 = sK5 ),
% 23.31/3.49      inference(resolution,[status(thm)],[c_2871,c_27]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_26,plain,
% 23.31/3.49      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 23.31/3.49      inference(cnf_transformation,[],[f116]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_1,plain,
% 23.31/3.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 23.31/3.49      inference(cnf_transformation,[],[f59]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2028,plain,
% 23.31/3.49      ( r1_tarski(sK0(k1_zfmisc_1(X0)),X0)
% 23.31/3.49      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 23.31/3.49      inference(resolution,[status(thm)],[c_26,c_1]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_34,plain,
% 23.31/3.49      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 23.31/3.49      inference(cnf_transformation,[],[f94]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2225,plain,
% 23.31/3.49      ( r1_tarski(sK0(k1_zfmisc_1(X0)),X0) ),
% 23.31/3.49      inference(global_propositional_subsumption,
% 23.31/3.49                [status(thm)],
% 23.31/3.49                [c_2028,c_34]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_3603,plain,
% 23.31/3.49      ( r1_tarski(sK0(k1_zfmisc_1(k1_tarski(X0))),k3_subset_1(sK4,sK5))
% 23.31/3.49      | ~ r2_hidden(X0,sK5)
% 23.31/3.49      | k1_xboole_0 = sK5 ),
% 23.31/3.49      inference(resolution,[status(thm)],[c_3038,c_2225]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_73875,plain,
% 23.31/3.49      ( r1_tarski(sK0(k1_zfmisc_1(k1_tarski(X0))),k3_subset_1(sK4,sK5))
% 23.31/3.49      | ~ r2_hidden(X0,sK5) ),
% 23.31/3.49      inference(backward_subsumption_resolution,
% 23.31/3.49                [status(thm)],
% 23.31/3.49                [c_73136,c_3603]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_33,plain,
% 23.31/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.31/3.49      | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) = k3_subset_1(X1,X0) ),
% 23.31/3.49      inference(cnf_transformation,[],[f107]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_37,negated_conjecture,
% 23.31/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 23.31/3.49      inference(cnf_transformation,[],[f95]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_482,plain,
% 23.31/3.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1)
% 23.31/3.49      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
% 23.31/3.49      | sK5 != X1 ),
% 23.31/3.49      inference(resolution_lifted,[status(thm)],[c_33,c_37]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_483,plain,
% 23.31/3.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,sK5),k2_xboole_0(X0,sK5))) = k3_subset_1(X0,sK5)
% 23.31/3.49      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
% 23.31/3.49      inference(unflattening,[status(thm)],[c_482]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_1775,plain,
% 23.31/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))) = k3_subset_1(sK4,sK5) ),
% 23.31/3.49      inference(equality_resolution,[status(thm)],[c_483]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2515,plain,
% 23.31/3.49      ( k1_tarski(X0) = k1_tarski(X0) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_840]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_1901,plain,
% 23.31/3.49      ( ~ r1_tarski(X0,X1)
% 23.31/3.49      | r1_tarski(k1_tarski(X2),X3)
% 23.31/3.49      | X3 != X1
% 23.31/3.49      | k1_tarski(X2) != X0 ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_846]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2514,plain,
% 23.31/3.49      ( ~ r1_tarski(k1_tarski(X0),X1)
% 23.31/3.49      | r1_tarski(k1_tarski(X0),X2)
% 23.31/3.49      | X2 != X1
% 23.31/3.49      | k1_tarski(X0) != k1_tarski(X0) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_1901]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_5273,plain,
% 23.31/3.49      ( r1_tarski(k1_tarski(X0),X1)
% 23.31/3.49      | ~ r1_tarski(k1_tarski(X0),k3_subset_1(sK4,sK5))
% 23.31/3.49      | X1 != k3_subset_1(sK4,sK5)
% 23.31/3.49      | k1_tarski(X0) != k1_tarski(X0) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_2514]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_36982,plain,
% 23.31/3.49      ( ~ r1_tarski(k1_tarski(X0),k3_subset_1(sK4,sK5))
% 23.31/3.49      | r1_tarski(k1_tarski(X0),k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))))
% 23.31/3.49      | k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))) != k3_subset_1(sK4,sK5)
% 23.31/3.49      | k1_tarski(X0) != k1_tarski(X0) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_5273]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_3593,plain,
% 23.31/3.49      ( r1_tarski(k1_tarski(X0),k3_subset_1(sK4,sK5))
% 23.31/3.49      | ~ r2_hidden(X0,sK5)
% 23.31/3.49      | k1_xboole_0 = sK5 ),
% 23.31/3.49      inference(resolution,[status(thm)],[c_3038,c_14]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_73839,plain,
% 23.31/3.49      ( r1_tarski(k1_tarski(X0),k3_subset_1(sK4,sK5))
% 23.31/3.49      | ~ r2_hidden(X0,sK5) ),
% 23.31/3.49      inference(backward_subsumption_resolution,
% 23.31/3.49                [status(thm)],
% 23.31/3.49                [c_73136,c_3593]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_7,plain,
% 23.31/3.49      ( ~ r2_hidden(X0,X1)
% 23.31/3.49      | ~ r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))) ),
% 23.31/3.49      inference(cnf_transformation,[],[f111]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_81016,plain,
% 23.31/3.49      ( ~ r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))))
% 23.31/3.49      | ~ r2_hidden(X0,sK5) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_7]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_28,plain,
% 23.31/3.49      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 23.31/3.49      inference(cnf_transformation,[],[f86]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_87421,plain,
% 23.31/3.49      ( ~ r1_tarski(k1_tarski(X0),k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5))))
% 23.31/3.49      | r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,sK5),k2_xboole_0(sK4,sK5)))) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_28]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_88652,plain,
% 23.31/3.49      ( ~ r2_hidden(X0,sK5) ),
% 23.31/3.49      inference(global_propositional_subsumption,
% 23.31/3.49                [status(thm)],
% 23.31/3.49                [c_73875,c_1775,c_2515,c_36982,c_73839,c_81016,c_87421]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_88724,plain,
% 23.31/3.49      ( v1_xboole_0(sK5) ),
% 23.31/3.49      inference(resolution,[status(thm)],[c_88652,c_1]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2,plain,
% 23.31/3.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 23.31/3.49      inference(cnf_transformation,[],[f58]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_3623,plain,
% 23.31/3.49      ( ~ r2_hidden(X0,sK5) | ~ v1_xboole_0(sK5) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_2]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_20362,plain,
% 23.31/3.49      ( ~ r2_hidden(sK2(X0,sK5),sK5) | ~ v1_xboole_0(sK5) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_3623]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_20364,plain,
% 23.31/3.49      ( ~ r2_hidden(sK2(k1_xboole_0,sK5),sK5) | ~ v1_xboole_0(sK5) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_20362]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_5240,plain,
% 23.31/3.49      ( ~ r2_hidden(sK2(X0,sK5),X0) | ~ v1_xboole_0(X0) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_2]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_5247,plain,
% 23.31/3.49      ( ~ r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0)
% 23.31/3.49      | ~ v1_xboole_0(k1_xboole_0) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_5240]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_841,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2783,plain,
% 23.31/3.49      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_841]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_2784,plain,
% 23.31/3.49      ( sK5 != k1_xboole_0
% 23.31/3.49      | k1_xboole_0 = sK5
% 23.31/3.49      | k1_xboole_0 != k1_xboole_0 ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_2783]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_11,plain,
% 23.31/3.49      ( r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X1 = X0 ),
% 23.31/3.49      inference(cnf_transformation,[],[f67]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_1955,plain,
% 23.31/3.49      ( r2_hidden(sK2(X0,sK5),X0)
% 23.31/3.49      | r2_hidden(sK2(X0,sK5),sK5)
% 23.31/3.49      | sK5 = X0 ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_11]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_1957,plain,
% 23.31/3.49      ( r2_hidden(sK2(k1_xboole_0,sK5),sK5)
% 23.31/3.49      | r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0)
% 23.31/3.49      | sK5 = k1_xboole_0 ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_1955]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_9,plain,
% 23.31/3.49      ( v1_xboole_0(k1_xboole_0) ),
% 23.31/3.49      inference(cnf_transformation,[],[f66]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_81,plain,
% 23.31/3.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_18]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_19,plain,
% 23.31/3.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 23.31/3.49      inference(cnf_transformation,[],[f77]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(c_78,plain,
% 23.31/3.49      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 23.31/3.49      | k1_xboole_0 = k1_xboole_0 ),
% 23.31/3.49      inference(instantiation,[status(thm)],[c_19]) ).
% 23.31/3.49  
% 23.31/3.49  cnf(contradiction,plain,
% 23.31/3.49      ( $false ),
% 23.31/3.49      inference(minisat,
% 23.31/3.49                [status(thm)],
% 23.31/3.49                [c_88724,c_20364,c_15595,c_5247,c_2784,c_1957,c_9,c_81,
% 23.31/3.49                 c_78,c_40]) ).
% 23.31/3.49  
% 23.31/3.49  
% 23.31/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.31/3.49  
% 23.31/3.49  ------                               Statistics
% 23.31/3.49  
% 23.31/3.49  ------ Selected
% 23.31/3.49  
% 23.31/3.49  total_time:                             2.609
% 23.31/3.49  
%------------------------------------------------------------------------------
