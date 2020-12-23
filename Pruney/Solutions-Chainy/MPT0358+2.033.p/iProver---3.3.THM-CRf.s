%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:54 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  154 (2343 expanded)
%              Number of clauses        :   83 ( 898 expanded)
%              Number of leaves         :   20 ( 435 expanded)
%              Depth                    :   28
%              Number of atoms          :  447 (7288 expanded)
%              Number of equality atoms :  169 (2476 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f38])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK5) != sK6
        | ~ r1_tarski(sK6,k3_subset_1(sK5,sK6)) )
      & ( k1_subset_1(sK5) = sK6
        | r1_tarski(sK6,k3_subset_1(sK5,sK6)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( k1_subset_1(sK5) != sK6
      | ~ r1_tarski(sK6,k3_subset_1(sK5,sK6)) )
    & ( k1_subset_1(sK5) = sK6
      | r1_tarski(sK6,k3_subset_1(sK5,sK6)) )
    & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f49,f50])).

fof(f86,plain,
    ( k1_subset_1(sK5) = sK6
    | r1_tarski(sK6,k3_subset_1(sK5,sK6)) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,
    ( k1_xboole_0 = sK6
    | r1_tarski(sK6,k3_subset_1(sK5,sK6)) ),
    inference(definition_unfolding,[],[f86,f82])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f36])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
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

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f104,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f87,plain,
    ( k1_subset_1(sK5) != sK6
    | ~ r1_tarski(sK6,k3_subset_1(sK5,sK6)) ),
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,
    ( k1_xboole_0 != sK6
    | ~ r1_tarski(sK6,k3_subset_1(sK5,sK6)) ),
    inference(definition_unfolding,[],[f87,f82])).

cnf(c_13,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1568,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1566,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK6,k3_subset_1(sK5,sK6))
    | k1_xboole_0 = sK6 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1557,plain,
    ( k1_xboole_0 = sK6
    | r1_tarski(sK6,k3_subset_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_584,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_585,plain,
    ( k3_subset_1(X0,sK6) = k4_xboole_0(X0,sK6)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_1649,plain,
    ( k3_subset_1(sK5,sK6) = k4_xboole_0(sK5,sK6) ),
    inference(equality_resolution,[status(thm)],[c_585])).

cnf(c_1795,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK6,k4_xboole_0(sK5,sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1557,c_1649])).

cnf(c_19,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_261,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_20,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_503,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 != X2
    | k4_xboole_0(X3,X1) != X4
    | k4_xboole_0(X2,X4) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_261,c_20])).

cnf(c_504,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_1556,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_2595,plain,
    ( k4_xboole_0(sK6,k4_xboole_0(X0,k4_xboole_0(sK5,sK6))) = sK6
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1795,c_1556])).

cnf(c_1563,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2863,plain,
    ( sK6 = k1_xboole_0
    | r1_xboole_0(X0,sK6) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2595,c_1563])).

cnf(c_2971,plain,
    ( sK6 = k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK5,sK6)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_2863])).

cnf(c_78,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_82,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_85,plain,
    ( r2_hidden(sK3(sK6),sK6)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1701,plain,
    ( ~ r1_xboole_0(sK6,X0)
    | ~ r2_hidden(sK3(sK6),X0)
    | ~ r2_hidden(sK3(sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1703,plain,
    ( ~ r1_xboole_0(sK6,sK6)
    | ~ r2_hidden(sK3(sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_571,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK5) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_33])).

cnf(c_572,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(sK5))
    | v1_xboole_0(k1_zfmisc_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_30,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_578,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(sK5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_572,c_30])).

cnf(c_1555,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1559,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2301,plain,
    ( r1_tarski(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1559])).

cnf(c_2305,plain,
    ( r1_tarski(sK6,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2301])).

cnf(c_948,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2623,plain,
    ( sK6 != X0
    | sK6 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_2624,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2623])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2628,plain,
    ( k4_xboole_0(sK6,k4_xboole_0(sK5,sK6)) = k5_xboole_0(sK6,sK6)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2595,c_0])).

cnf(c_2593,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1566,c_1556])).

cnf(c_2629,plain,
    ( k5_xboole_0(sK6,sK6) = sK6
    | sK6 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2628,c_2593])).

cnf(c_2594,plain,
    ( k4_xboole_0(sK6,k4_xboole_0(X0,sK5)) = sK6 ),
    inference(superposition,[status(thm)],[c_2301,c_1556])).

cnf(c_3022,plain,
    ( k5_xboole_0(sK6,sK6) = k4_xboole_0(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_2594,c_0])).

cnf(c_3031,plain,
    ( k4_xboole_0(sK6,sK5) = sK6
    | sK6 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2629,c_3022])).

cnf(c_3034,plain,
    ( sK6 = k1_xboole_0
    | r1_xboole_0(X0,sK6) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3031,c_1563])).

cnf(c_3038,plain,
    ( r1_xboole_0(X0,sK6)
    | ~ r1_tarski(X0,sK5)
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3034])).

cnf(c_3040,plain,
    ( r1_xboole_0(sK6,sK6)
    | ~ r1_tarski(sK6,sK5)
    | sK6 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3038])).

cnf(c_3122,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2971,c_78,c_82,c_85,c_1703,c_2305,c_2624,c_3040])).

cnf(c_3125,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3122,c_2594])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1572,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4492,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3125,c_1572])).

cnf(c_18,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1565,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3020,plain,
    ( r1_xboole_0(sK6,k4_xboole_0(X0,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2594,c_1565])).

cnf(c_4062,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3020,c_3122])).

cnf(c_1571,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4235,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,sK5)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4062,c_1571])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1573,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4489,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,sK5)) = iProver_top
    | r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3125,c_1573])).

cnf(c_4678,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4492,c_4235,c_4489])).

cnf(c_4689,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1568,c_4678])).

cnf(c_3021,plain,
    ( k4_xboole_0(sK6,k4_xboole_0(X0,sK5)) = k5_xboole_0(sK6,k4_xboole_0(sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_2594,c_0])).

cnf(c_3024,plain,
    ( k5_xboole_0(sK6,k4_xboole_0(sK6,sK6)) = sK6 ),
    inference(demodulation,[status(thm)],[c_3021,c_2594])).

cnf(c_4172,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3024,c_3024,c_3122])).

cnf(c_4848,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4689,c_4172])).

cnf(c_3481,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK5) ),
    inference(light_normalisation,[status(thm)],[c_3022,c_3022,c_3122])).

cnf(c_5103,plain,
    ( k4_xboole_0(k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4848,c_3481])).

cnf(c_5413,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = sK5 ),
    inference(superposition,[status(thm)],[c_5103,c_2593])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(sK6,k3_subset_1(sK5,sK6))
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1558,plain,
    ( k1_xboole_0 != sK6
    | r1_tarski(sK6,k3_subset_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1797,plain,
    ( sK6 != k1_xboole_0
    | r1_tarski(sK6,k4_xboole_0(sK5,sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1649,c_1558])).

cnf(c_3131,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k4_xboole_0(sK5,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3122,c_1797])).

cnf(c_3134,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(sK5,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3131])).

cnf(c_5709,plain,
    ( r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5413,c_3134])).

cnf(c_3128,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3122,c_2301])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5709,c_3128])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.52/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.98  
% 3.52/0.98  ------  iProver source info
% 3.52/0.98  
% 3.52/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.98  git: non_committed_changes: false
% 3.52/0.98  git: last_make_outside_of_git: false
% 3.52/0.98  
% 3.52/0.98  ------ 
% 3.52/0.98  
% 3.52/0.98  ------ Input Options
% 3.52/0.98  
% 3.52/0.98  --out_options                           all
% 3.52/0.98  --tptp_safe_out                         true
% 3.52/0.98  --problem_path                          ""
% 3.52/0.98  --include_path                          ""
% 3.52/0.98  --clausifier                            res/vclausify_rel
% 3.52/0.98  --clausifier_options                    ""
% 3.52/0.98  --stdin                                 false
% 3.52/0.98  --stats_out                             all
% 3.52/0.98  
% 3.52/0.98  ------ General Options
% 3.52/0.98  
% 3.52/0.98  --fof                                   false
% 3.52/0.98  --time_out_real                         305.
% 3.52/0.98  --time_out_virtual                      -1.
% 3.52/0.98  --symbol_type_check                     false
% 3.52/0.98  --clausify_out                          false
% 3.52/0.98  --sig_cnt_out                           false
% 3.52/0.98  --trig_cnt_out                          false
% 3.52/0.98  --trig_cnt_out_tolerance                1.
% 3.52/0.98  --trig_cnt_out_sk_spl                   false
% 3.52/0.98  --abstr_cl_out                          false
% 3.52/0.98  
% 3.52/0.98  ------ Global Options
% 3.52/0.98  
% 3.52/0.98  --schedule                              default
% 3.52/0.98  --add_important_lit                     false
% 3.52/0.98  --prop_solver_per_cl                    1000
% 3.52/0.98  --min_unsat_core                        false
% 3.52/0.98  --soft_assumptions                      false
% 3.52/0.98  --soft_lemma_size                       3
% 3.52/0.98  --prop_impl_unit_size                   0
% 3.52/0.98  --prop_impl_unit                        []
% 3.52/0.98  --share_sel_clauses                     true
% 3.52/0.98  --reset_solvers                         false
% 3.52/0.98  --bc_imp_inh                            [conj_cone]
% 3.52/0.98  --conj_cone_tolerance                   3.
% 3.52/0.98  --extra_neg_conj                        none
% 3.52/0.98  --large_theory_mode                     true
% 3.52/0.98  --prolific_symb_bound                   200
% 3.52/0.98  --lt_threshold                          2000
% 3.52/0.98  --clause_weak_htbl                      true
% 3.52/0.98  --gc_record_bc_elim                     false
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing Options
% 3.52/0.98  
% 3.52/0.98  --preprocessing_flag                    true
% 3.52/0.98  --time_out_prep_mult                    0.1
% 3.52/0.98  --splitting_mode                        input
% 3.52/0.98  --splitting_grd                         true
% 3.52/0.98  --splitting_cvd                         false
% 3.52/0.98  --splitting_cvd_svl                     false
% 3.52/0.98  --splitting_nvd                         32
% 3.52/0.98  --sub_typing                            true
% 3.52/0.98  --prep_gs_sim                           true
% 3.52/0.98  --prep_unflatten                        true
% 3.52/0.98  --prep_res_sim                          true
% 3.52/0.98  --prep_upred                            true
% 3.52/0.98  --prep_sem_filter                       exhaustive
% 3.52/0.98  --prep_sem_filter_out                   false
% 3.52/0.98  --pred_elim                             true
% 3.52/0.98  --res_sim_input                         true
% 3.52/0.98  --eq_ax_congr_red                       true
% 3.52/0.98  --pure_diseq_elim                       true
% 3.52/0.98  --brand_transform                       false
% 3.52/0.98  --non_eq_to_eq                          false
% 3.52/0.98  --prep_def_merge                        true
% 3.52/0.98  --prep_def_merge_prop_impl              false
% 3.52/0.98  --prep_def_merge_mbd                    true
% 3.52/0.98  --prep_def_merge_tr_red                 false
% 3.52/0.98  --prep_def_merge_tr_cl                  false
% 3.52/0.98  --smt_preprocessing                     true
% 3.52/0.98  --smt_ac_axioms                         fast
% 3.52/0.98  --preprocessed_out                      false
% 3.52/0.98  --preprocessed_stats                    false
% 3.52/0.98  
% 3.52/0.98  ------ Abstraction refinement Options
% 3.52/0.98  
% 3.52/0.98  --abstr_ref                             []
% 3.52/0.98  --abstr_ref_prep                        false
% 3.52/0.98  --abstr_ref_until_sat                   false
% 3.52/0.98  --abstr_ref_sig_restrict                funpre
% 3.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.98  --abstr_ref_under                       []
% 3.52/0.98  
% 3.52/0.98  ------ SAT Options
% 3.52/0.98  
% 3.52/0.98  --sat_mode                              false
% 3.52/0.98  --sat_fm_restart_options                ""
% 3.52/0.98  --sat_gr_def                            false
% 3.52/0.98  --sat_epr_types                         true
% 3.52/0.98  --sat_non_cyclic_types                  false
% 3.52/0.98  --sat_finite_models                     false
% 3.52/0.98  --sat_fm_lemmas                         false
% 3.52/0.98  --sat_fm_prep                           false
% 3.52/0.98  --sat_fm_uc_incr                        true
% 3.52/0.98  --sat_out_model                         small
% 3.52/0.98  --sat_out_clauses                       false
% 3.52/0.98  
% 3.52/0.98  ------ QBF Options
% 3.52/0.98  
% 3.52/0.98  --qbf_mode                              false
% 3.52/0.98  --qbf_elim_univ                         false
% 3.52/0.98  --qbf_dom_inst                          none
% 3.52/0.98  --qbf_dom_pre_inst                      false
% 3.52/0.98  --qbf_sk_in                             false
% 3.52/0.98  --qbf_pred_elim                         true
% 3.52/0.98  --qbf_split                             512
% 3.52/0.98  
% 3.52/0.98  ------ BMC1 Options
% 3.52/0.98  
% 3.52/0.98  --bmc1_incremental                      false
% 3.52/0.98  --bmc1_axioms                           reachable_all
% 3.52/0.98  --bmc1_min_bound                        0
% 3.52/0.98  --bmc1_max_bound                        -1
% 3.52/0.98  --bmc1_max_bound_default                -1
% 3.52/0.98  --bmc1_symbol_reachability              true
% 3.52/0.98  --bmc1_property_lemmas                  false
% 3.52/0.98  --bmc1_k_induction                      false
% 3.52/0.98  --bmc1_non_equiv_states                 false
% 3.52/0.98  --bmc1_deadlock                         false
% 3.52/0.98  --bmc1_ucm                              false
% 3.52/0.98  --bmc1_add_unsat_core                   none
% 3.52/0.98  --bmc1_unsat_core_children              false
% 3.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.98  --bmc1_out_stat                         full
% 3.52/0.98  --bmc1_ground_init                      false
% 3.52/0.98  --bmc1_pre_inst_next_state              false
% 3.52/0.98  --bmc1_pre_inst_state                   false
% 3.52/0.98  --bmc1_pre_inst_reach_state             false
% 3.52/0.98  --bmc1_out_unsat_core                   false
% 3.52/0.98  --bmc1_aig_witness_out                  false
% 3.52/0.98  --bmc1_verbose                          false
% 3.52/0.98  --bmc1_dump_clauses_tptp                false
% 3.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.98  --bmc1_dump_file                        -
% 3.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.98  --bmc1_ucm_extend_mode                  1
% 3.52/0.98  --bmc1_ucm_init_mode                    2
% 3.52/0.98  --bmc1_ucm_cone_mode                    none
% 3.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.98  --bmc1_ucm_relax_model                  4
% 3.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.98  --bmc1_ucm_layered_model                none
% 3.52/0.98  --bmc1_ucm_max_lemma_size               10
% 3.52/0.98  
% 3.52/0.98  ------ AIG Options
% 3.52/0.98  
% 3.52/0.98  --aig_mode                              false
% 3.52/0.98  
% 3.52/0.98  ------ Instantiation Options
% 3.52/0.98  
% 3.52/0.98  --instantiation_flag                    true
% 3.52/0.98  --inst_sos_flag                         true
% 3.52/0.98  --inst_sos_phase                        true
% 3.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.98  --inst_lit_sel_side                     num_symb
% 3.52/0.98  --inst_solver_per_active                1400
% 3.52/0.98  --inst_solver_calls_frac                1.
% 3.52/0.98  --inst_passive_queue_type               priority_queues
% 3.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.98  --inst_passive_queues_freq              [25;2]
% 3.52/0.98  --inst_dismatching                      true
% 3.52/0.98  --inst_eager_unprocessed_to_passive     true
% 3.52/0.98  --inst_prop_sim_given                   true
% 3.52/0.98  --inst_prop_sim_new                     false
% 3.52/0.98  --inst_subs_new                         false
% 3.52/0.98  --inst_eq_res_simp                      false
% 3.52/0.98  --inst_subs_given                       false
% 3.52/0.98  --inst_orphan_elimination               true
% 3.52/0.98  --inst_learning_loop_flag               true
% 3.52/0.98  --inst_learning_start                   3000
% 3.52/0.98  --inst_learning_factor                  2
% 3.52/0.98  --inst_start_prop_sim_after_learn       3
% 3.52/0.98  --inst_sel_renew                        solver
% 3.52/0.98  --inst_lit_activity_flag                true
% 3.52/0.98  --inst_restr_to_given                   false
% 3.52/0.98  --inst_activity_threshold               500
% 3.52/0.98  --inst_out_proof                        true
% 3.52/0.98  
% 3.52/0.98  ------ Resolution Options
% 3.52/0.98  
% 3.52/0.98  --resolution_flag                       true
% 3.52/0.98  --res_lit_sel                           adaptive
% 3.52/0.98  --res_lit_sel_side                      none
% 3.52/0.98  --res_ordering                          kbo
% 3.52/0.98  --res_to_prop_solver                    active
% 3.52/0.98  --res_prop_simpl_new                    false
% 3.52/0.98  --res_prop_simpl_given                  true
% 3.52/0.98  --res_passive_queue_type                priority_queues
% 3.52/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.98  --res_passive_queues_freq               [15;5]
% 3.52/0.98  --res_forward_subs                      full
% 3.52/0.98  --res_backward_subs                     full
% 3.52/0.98  --res_forward_subs_resolution           true
% 3.52/0.98  --res_backward_subs_resolution          true
% 3.52/0.98  --res_orphan_elimination                true
% 3.52/0.98  --res_time_limit                        2.
% 3.52/0.98  --res_out_proof                         true
% 3.52/0.98  
% 3.52/0.98  ------ Superposition Options
% 3.52/0.98  
% 3.52/0.98  --superposition_flag                    true
% 3.52/0.98  --sup_passive_queue_type                priority_queues
% 3.52/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.98  --demod_completeness_check              fast
% 3.52/0.98  --demod_use_ground                      true
% 3.52/0.98  --sup_to_prop_solver                    passive
% 3.52/0.98  --sup_prop_simpl_new                    true
% 3.52/0.98  --sup_prop_simpl_given                  true
% 3.52/0.98  --sup_fun_splitting                     true
% 3.52/0.98  --sup_smt_interval                      50000
% 3.52/0.98  
% 3.52/0.98  ------ Superposition Simplification Setup
% 3.52/0.98  
% 3.52/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.52/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.52/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.52/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.52/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.52/0.98  --sup_immed_triv                        [TrivRules]
% 3.52/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.98  --sup_immed_bw_main                     []
% 3.52/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.52/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.98  --sup_input_bw                          []
% 3.52/0.98  
% 3.52/0.98  ------ Combination Options
% 3.52/0.98  
% 3.52/0.98  --comb_res_mult                         3
% 3.52/0.98  --comb_sup_mult                         2
% 3.52/0.98  --comb_inst_mult                        10
% 3.52/0.98  
% 3.52/0.98  ------ Debug Options
% 3.52/0.98  
% 3.52/0.98  --dbg_backtrace                         false
% 3.52/0.98  --dbg_dump_prop_clauses                 false
% 3.52/0.98  --dbg_dump_prop_clauses_file            -
% 3.52/0.98  --dbg_out_stat                          false
% 3.52/0.98  ------ Parsing...
% 3.52/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.98  ------ Proving...
% 3.52/0.98  ------ Problem Properties 
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  clauses                                 29
% 3.52/0.98  conjectures                             2
% 3.52/0.98  EPR                                     4
% 3.52/0.98  Horn                                    21
% 3.52/0.98  unary                                   3
% 3.52/0.98  binary                                  17
% 3.52/0.98  lits                                    65
% 3.52/0.98  lits eq                                 16
% 3.52/0.98  fd_pure                                 0
% 3.52/0.98  fd_pseudo                               0
% 3.52/0.98  fd_cond                                 1
% 3.52/0.98  fd_pseudo_cond                          6
% 3.52/0.98  AC symbols                              0
% 3.52/0.98  
% 3.52/0.98  ------ Schedule dynamic 5 is on 
% 3.52/0.98  
% 3.52/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  ------ 
% 3.52/0.98  Current options:
% 3.52/0.98  ------ 
% 3.52/0.98  
% 3.52/0.98  ------ Input Options
% 3.52/0.98  
% 3.52/0.98  --out_options                           all
% 3.52/0.98  --tptp_safe_out                         true
% 3.52/0.98  --problem_path                          ""
% 3.52/0.98  --include_path                          ""
% 3.52/0.98  --clausifier                            res/vclausify_rel
% 3.52/0.98  --clausifier_options                    ""
% 3.52/0.98  --stdin                                 false
% 3.52/0.98  --stats_out                             all
% 3.52/0.98  
% 3.52/0.98  ------ General Options
% 3.52/0.98  
% 3.52/0.98  --fof                                   false
% 3.52/0.98  --time_out_real                         305.
% 3.52/0.98  --time_out_virtual                      -1.
% 3.52/0.98  --symbol_type_check                     false
% 3.52/0.98  --clausify_out                          false
% 3.52/0.98  --sig_cnt_out                           false
% 3.52/0.98  --trig_cnt_out                          false
% 3.52/0.98  --trig_cnt_out_tolerance                1.
% 3.52/0.98  --trig_cnt_out_sk_spl                   false
% 3.52/0.98  --abstr_cl_out                          false
% 3.52/0.98  
% 3.52/0.98  ------ Global Options
% 3.52/0.98  
% 3.52/0.98  --schedule                              default
% 3.52/0.98  --add_important_lit                     false
% 3.52/0.98  --prop_solver_per_cl                    1000
% 3.52/0.98  --min_unsat_core                        false
% 3.52/0.98  --soft_assumptions                      false
% 3.52/0.98  --soft_lemma_size                       3
% 3.52/0.98  --prop_impl_unit_size                   0
% 3.52/0.98  --prop_impl_unit                        []
% 3.52/0.98  --share_sel_clauses                     true
% 3.52/0.98  --reset_solvers                         false
% 3.52/0.98  --bc_imp_inh                            [conj_cone]
% 3.52/0.98  --conj_cone_tolerance                   3.
% 3.52/0.98  --extra_neg_conj                        none
% 3.52/0.98  --large_theory_mode                     true
% 3.52/0.98  --prolific_symb_bound                   200
% 3.52/0.98  --lt_threshold                          2000
% 3.52/0.98  --clause_weak_htbl                      true
% 3.52/0.98  --gc_record_bc_elim                     false
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing Options
% 3.52/0.98  
% 3.52/0.98  --preprocessing_flag                    true
% 3.52/0.98  --time_out_prep_mult                    0.1
% 3.52/0.98  --splitting_mode                        input
% 3.52/0.98  --splitting_grd                         true
% 3.52/0.98  --splitting_cvd                         false
% 3.52/0.98  --splitting_cvd_svl                     false
% 3.52/0.98  --splitting_nvd                         32
% 3.52/0.98  --sub_typing                            true
% 3.52/0.98  --prep_gs_sim                           true
% 3.52/0.98  --prep_unflatten                        true
% 3.52/0.98  --prep_res_sim                          true
% 3.52/0.98  --prep_upred                            true
% 3.52/0.98  --prep_sem_filter                       exhaustive
% 3.52/0.98  --prep_sem_filter_out                   false
% 3.52/0.98  --pred_elim                             true
% 3.52/0.98  --res_sim_input                         true
% 3.52/0.98  --eq_ax_congr_red                       true
% 3.52/0.98  --pure_diseq_elim                       true
% 3.52/0.98  --brand_transform                       false
% 3.52/0.98  --non_eq_to_eq                          false
% 3.52/0.98  --prep_def_merge                        true
% 3.52/0.98  --prep_def_merge_prop_impl              false
% 3.52/0.98  --prep_def_merge_mbd                    true
% 3.52/0.98  --prep_def_merge_tr_red                 false
% 3.52/0.98  --prep_def_merge_tr_cl                  false
% 3.52/0.98  --smt_preprocessing                     true
% 3.52/0.98  --smt_ac_axioms                         fast
% 3.52/0.98  --preprocessed_out                      false
% 3.52/0.98  --preprocessed_stats                    false
% 3.52/0.98  
% 3.52/0.98  ------ Abstraction refinement Options
% 3.52/0.98  
% 3.52/0.98  --abstr_ref                             []
% 3.52/0.98  --abstr_ref_prep                        false
% 3.52/0.98  --abstr_ref_until_sat                   false
% 3.52/0.98  --abstr_ref_sig_restrict                funpre
% 3.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.98  --abstr_ref_under                       []
% 3.52/0.98  
% 3.52/0.98  ------ SAT Options
% 3.52/0.98  
% 3.52/0.98  --sat_mode                              false
% 3.52/0.98  --sat_fm_restart_options                ""
% 3.52/0.98  --sat_gr_def                            false
% 3.52/0.98  --sat_epr_types                         true
% 3.52/0.98  --sat_non_cyclic_types                  false
% 3.52/0.98  --sat_finite_models                     false
% 3.52/0.98  --sat_fm_lemmas                         false
% 3.52/0.98  --sat_fm_prep                           false
% 3.52/0.98  --sat_fm_uc_incr                        true
% 3.52/0.98  --sat_out_model                         small
% 3.52/0.98  --sat_out_clauses                       false
% 3.52/0.98  
% 3.52/0.98  ------ QBF Options
% 3.52/0.98  
% 3.52/0.98  --qbf_mode                              false
% 3.52/0.98  --qbf_elim_univ                         false
% 3.52/0.98  --qbf_dom_inst                          none
% 3.52/0.98  --qbf_dom_pre_inst                      false
% 3.52/0.98  --qbf_sk_in                             false
% 3.52/0.98  --qbf_pred_elim                         true
% 3.52/0.98  --qbf_split                             512
% 3.52/0.98  
% 3.52/0.98  ------ BMC1 Options
% 3.52/0.98  
% 3.52/0.98  --bmc1_incremental                      false
% 3.52/0.98  --bmc1_axioms                           reachable_all
% 3.52/0.98  --bmc1_min_bound                        0
% 3.52/0.98  --bmc1_max_bound                        -1
% 3.52/0.98  --bmc1_max_bound_default                -1
% 3.52/0.98  --bmc1_symbol_reachability              true
% 3.52/0.98  --bmc1_property_lemmas                  false
% 3.52/0.98  --bmc1_k_induction                      false
% 3.52/0.98  --bmc1_non_equiv_states                 false
% 3.52/0.98  --bmc1_deadlock                         false
% 3.52/0.98  --bmc1_ucm                              false
% 3.52/0.98  --bmc1_add_unsat_core                   none
% 3.52/0.98  --bmc1_unsat_core_children              false
% 3.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.98  --bmc1_out_stat                         full
% 3.52/0.98  --bmc1_ground_init                      false
% 3.52/0.98  --bmc1_pre_inst_next_state              false
% 3.52/0.98  --bmc1_pre_inst_state                   false
% 3.52/0.98  --bmc1_pre_inst_reach_state             false
% 3.52/0.98  --bmc1_out_unsat_core                   false
% 3.52/0.98  --bmc1_aig_witness_out                  false
% 3.52/0.98  --bmc1_verbose                          false
% 3.52/0.98  --bmc1_dump_clauses_tptp                false
% 3.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.98  --bmc1_dump_file                        -
% 3.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.98  --bmc1_ucm_extend_mode                  1
% 3.52/0.98  --bmc1_ucm_init_mode                    2
% 3.52/0.98  --bmc1_ucm_cone_mode                    none
% 3.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.98  --bmc1_ucm_relax_model                  4
% 3.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.98  --bmc1_ucm_layered_model                none
% 3.52/0.98  --bmc1_ucm_max_lemma_size               10
% 3.52/0.98  
% 3.52/0.98  ------ AIG Options
% 3.52/0.98  
% 3.52/0.98  --aig_mode                              false
% 3.52/0.98  
% 3.52/0.98  ------ Instantiation Options
% 3.52/0.98  
% 3.52/0.98  --instantiation_flag                    true
% 3.52/0.98  --inst_sos_flag                         true
% 3.52/0.98  --inst_sos_phase                        true
% 3.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.98  --inst_lit_sel_side                     none
% 3.52/0.98  --inst_solver_per_active                1400
% 3.52/0.98  --inst_solver_calls_frac                1.
% 3.52/0.98  --inst_passive_queue_type               priority_queues
% 3.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.98  --inst_passive_queues_freq              [25;2]
% 3.52/0.98  --inst_dismatching                      true
% 3.52/0.98  --inst_eager_unprocessed_to_passive     true
% 3.52/0.98  --inst_prop_sim_given                   true
% 3.52/0.98  --inst_prop_sim_new                     false
% 3.52/0.98  --inst_subs_new                         false
% 3.52/0.98  --inst_eq_res_simp                      false
% 3.52/0.98  --inst_subs_given                       false
% 3.52/0.98  --inst_orphan_elimination               true
% 3.52/0.98  --inst_learning_loop_flag               true
% 3.52/0.98  --inst_learning_start                   3000
% 3.52/0.98  --inst_learning_factor                  2
% 3.52/0.98  --inst_start_prop_sim_after_learn       3
% 3.52/0.98  --inst_sel_renew                        solver
% 3.52/0.98  --inst_lit_activity_flag                true
% 3.52/0.98  --inst_restr_to_given                   false
% 3.52/0.98  --inst_activity_threshold               500
% 3.52/0.98  --inst_out_proof                        true
% 3.52/0.98  
% 3.52/0.98  ------ Resolution Options
% 3.52/0.98  
% 3.52/0.98  --resolution_flag                       false
% 3.52/0.98  --res_lit_sel                           adaptive
% 3.52/0.98  --res_lit_sel_side                      none
% 3.52/0.98  --res_ordering                          kbo
% 3.52/0.98  --res_to_prop_solver                    active
% 3.52/0.98  --res_prop_simpl_new                    false
% 3.52/0.98  --res_prop_simpl_given                  true
% 3.52/0.98  --res_passive_queue_type                priority_queues
% 3.52/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.98  --res_passive_queues_freq               [15;5]
% 3.52/0.98  --res_forward_subs                      full
% 3.52/0.98  --res_backward_subs                     full
% 3.52/0.98  --res_forward_subs_resolution           true
% 3.52/0.98  --res_backward_subs_resolution          true
% 3.52/0.98  --res_orphan_elimination                true
% 3.52/0.98  --res_time_limit                        2.
% 3.52/0.98  --res_out_proof                         true
% 3.52/0.98  
% 3.52/0.98  ------ Superposition Options
% 3.52/0.98  
% 3.52/0.98  --superposition_flag                    true
% 3.52/0.98  --sup_passive_queue_type                priority_queues
% 3.52/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.98  --demod_completeness_check              fast
% 3.52/0.98  --demod_use_ground                      true
% 3.52/0.98  --sup_to_prop_solver                    passive
% 3.52/0.98  --sup_prop_simpl_new                    true
% 3.52/0.98  --sup_prop_simpl_given                  true
% 3.52/0.98  --sup_fun_splitting                     true
% 3.52/0.98  --sup_smt_interval                      50000
% 3.52/0.98  
% 3.52/0.98  ------ Superposition Simplification Setup
% 3.52/0.98  
% 3.52/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.52/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.52/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.52/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.52/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.52/0.98  --sup_immed_triv                        [TrivRules]
% 3.52/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.98  --sup_immed_bw_main                     []
% 3.52/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.52/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.98  --sup_input_bw                          []
% 3.52/0.98  
% 3.52/0.98  ------ Combination Options
% 3.52/0.98  
% 3.52/0.98  --comb_res_mult                         3
% 3.52/0.98  --comb_sup_mult                         2
% 3.52/0.98  --comb_inst_mult                        10
% 3.52/0.98  
% 3.52/0.98  ------ Debug Options
% 3.52/0.98  
% 3.52/0.98  --dbg_backtrace                         false
% 3.52/0.98  --dbg_dump_prop_clauses                 false
% 3.52/0.98  --dbg_dump_prop_clauses_file            -
% 3.52/0.98  --dbg_out_stat                          false
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  ------ Proving...
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  % SZS status Theorem for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  fof(f4,axiom,(
% 3.52/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f21,plain,(
% 3.52/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.52/0.98    inference(ennf_transformation,[],[f4])).
% 3.52/0.98  
% 3.52/0.98  fof(f38,plain,(
% 3.52/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f39,plain,(
% 3.52/0.98    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f38])).
% 3.52/0.98  
% 3.52/0.98  fof(f64,plain,(
% 3.52/0.98    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 3.52/0.98    inference(cnf_transformation,[],[f39])).
% 3.52/0.98  
% 3.52/0.98  fof(f5,axiom,(
% 3.52/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f40,plain,(
% 3.52/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/0.98    inference(nnf_transformation,[],[f5])).
% 3.52/0.98  
% 3.52/0.98  fof(f41,plain,(
% 3.52/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/0.98    inference(flattening,[],[f40])).
% 3.52/0.98  
% 3.52/0.98  fof(f65,plain,(
% 3.52/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.52/0.98    inference(cnf_transformation,[],[f41])).
% 3.52/0.98  
% 3.52/0.98  fof(f102,plain,(
% 3.52/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.52/0.98    inference(equality_resolution,[],[f65])).
% 3.52/0.98  
% 3.52/0.98  fof(f16,conjecture,(
% 3.52/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f17,negated_conjecture,(
% 3.52/0.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.52/0.98    inference(negated_conjecture,[],[f16])).
% 3.52/0.98  
% 3.52/0.98  fof(f26,plain,(
% 3.52/0.98    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f17])).
% 3.52/0.98  
% 3.52/0.98  fof(f48,plain,(
% 3.52/0.98    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/0.98    inference(nnf_transformation,[],[f26])).
% 3.52/0.98  
% 3.52/0.98  fof(f49,plain,(
% 3.52/0.98    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/0.98    inference(flattening,[],[f48])).
% 3.52/0.98  
% 3.52/0.98  fof(f50,plain,(
% 3.52/0.98    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK5) != sK6 | ~r1_tarski(sK6,k3_subset_1(sK5,sK6))) & (k1_subset_1(sK5) = sK6 | r1_tarski(sK6,k3_subset_1(sK5,sK6))) & m1_subset_1(sK6,k1_zfmisc_1(sK5)))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f51,plain,(
% 3.52/0.98    (k1_subset_1(sK5) != sK6 | ~r1_tarski(sK6,k3_subset_1(sK5,sK6))) & (k1_subset_1(sK5) = sK6 | r1_tarski(sK6,k3_subset_1(sK5,sK6))) & m1_subset_1(sK6,k1_zfmisc_1(sK5))),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f49,f50])).
% 3.52/0.98  
% 3.52/0.98  fof(f86,plain,(
% 3.52/0.98    k1_subset_1(sK5) = sK6 | r1_tarski(sK6,k3_subset_1(sK5,sK6))),
% 3.52/0.98    inference(cnf_transformation,[],[f51])).
% 3.52/0.98  
% 3.52/0.98  fof(f13,axiom,(
% 3.52/0.98    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f82,plain,(
% 3.52/0.98    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f13])).
% 3.52/0.98  
% 3.52/0.98  fof(f97,plain,(
% 3.52/0.98    k1_xboole_0 = sK6 | r1_tarski(sK6,k3_subset_1(sK5,sK6))),
% 3.52/0.98    inference(definition_unfolding,[],[f86,f82])).
% 3.52/0.98  
% 3.52/0.98  fof(f14,axiom,(
% 3.52/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f25,plain,(
% 3.52/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f14])).
% 3.52/0.98  
% 3.52/0.98  fof(f83,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f25])).
% 3.52/0.98  
% 3.52/0.98  fof(f85,plain,(
% 3.52/0.98    m1_subset_1(sK6,k1_zfmisc_1(sK5))),
% 3.52/0.98    inference(cnf_transformation,[],[f51])).
% 3.52/0.98  
% 3.52/0.98  fof(f9,axiom,(
% 3.52/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f42,plain,(
% 3.52/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.52/0.98    inference(nnf_transformation,[],[f9])).
% 3.52/0.98  
% 3.52/0.98  fof(f71,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f42])).
% 3.52/0.98  
% 3.52/0.98  fof(f10,axiom,(
% 3.52/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f23,plain,(
% 3.52/0.98    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.52/0.98    inference(ennf_transformation,[],[f10])).
% 3.52/0.98  
% 3.52/0.98  fof(f73,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f23])).
% 3.52/0.98  
% 3.52/0.98  fof(f67,plain,(
% 3.52/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f41])).
% 3.52/0.98  
% 3.52/0.98  fof(f3,axiom,(
% 3.52/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f18,plain,(
% 3.52/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.52/0.98    inference(rectify,[],[f3])).
% 3.52/0.98  
% 3.52/0.98  fof(f20,plain,(
% 3.52/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.52/0.98    inference(ennf_transformation,[],[f18])).
% 3.52/0.98  
% 3.52/0.98  fof(f36,plain,(
% 3.52/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f37,plain,(
% 3.52/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f36])).
% 3.52/0.98  
% 3.52/0.98  fof(f63,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f37])).
% 3.52/0.98  
% 3.52/0.98  fof(f12,axiom,(
% 3.52/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f24,plain,(
% 3.52/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f12])).
% 3.52/0.98  
% 3.52/0.98  fof(f47,plain,(
% 3.52/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.52/0.98    inference(nnf_transformation,[],[f24])).
% 3.52/0.98  
% 3.52/0.98  fof(f78,plain,(
% 3.52/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f47])).
% 3.52/0.98  
% 3.52/0.98  fof(f15,axiom,(
% 3.52/0.98    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f84,plain,(
% 3.52/0.98    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f15])).
% 3.52/0.98  
% 3.52/0.98  fof(f11,axiom,(
% 3.52/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f43,plain,(
% 3.52/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.52/0.98    inference(nnf_transformation,[],[f11])).
% 3.52/0.98  
% 3.52/0.98  fof(f44,plain,(
% 3.52/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.52/0.98    inference(rectify,[],[f43])).
% 3.52/0.98  
% 3.52/0.98  fof(f45,plain,(
% 3.52/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f46,plain,(
% 3.52/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).
% 3.52/0.98  
% 3.52/0.98  fof(f74,plain,(
% 3.52/0.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.52/0.98    inference(cnf_transformation,[],[f46])).
% 3.52/0.98  
% 3.52/0.98  fof(f104,plain,(
% 3.52/0.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.52/0.98    inference(equality_resolution,[],[f74])).
% 3.52/0.98  
% 3.52/0.98  fof(f6,axiom,(
% 3.52/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f68,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f6])).
% 3.52/0.98  
% 3.52/0.98  fof(f8,axiom,(
% 3.52/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f70,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f8])).
% 3.52/0.98  
% 3.52/0.98  fof(f88,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.52/0.98    inference(definition_unfolding,[],[f68,f70])).
% 3.52/0.98  
% 3.52/0.98  fof(f2,axiom,(
% 3.52/0.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f31,plain,(
% 3.52/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.52/0.98    inference(nnf_transformation,[],[f2])).
% 3.52/0.98  
% 3.52/0.98  fof(f32,plain,(
% 3.52/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.52/0.98    inference(flattening,[],[f31])).
% 3.52/0.98  
% 3.52/0.98  fof(f33,plain,(
% 3.52/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.52/0.98    inference(rectify,[],[f32])).
% 3.52/0.98  
% 3.52/0.98  fof(f34,plain,(
% 3.52/0.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f35,plain,(
% 3.52/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.52/0.98  
% 3.52/0.98  fof(f55,plain,(
% 3.52/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.52/0.98    inference(cnf_transformation,[],[f35])).
% 3.52/0.98  
% 3.52/0.98  fof(f94,plain,(
% 3.52/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 3.52/0.98    inference(definition_unfolding,[],[f55,f70])).
% 3.52/0.98  
% 3.52/0.98  fof(f100,plain,(
% 3.52/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.52/0.98    inference(equality_resolution,[],[f94])).
% 3.52/0.98  
% 3.52/0.98  fof(f72,plain,(
% 3.52/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.52/0.98    inference(cnf_transformation,[],[f42])).
% 3.52/0.98  
% 3.52/0.98  fof(f56,plain,(
% 3.52/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.52/0.98    inference(cnf_transformation,[],[f35])).
% 3.52/0.98  
% 3.52/0.98  fof(f93,plain,(
% 3.52/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 3.52/0.98    inference(definition_unfolding,[],[f56,f70])).
% 3.52/0.98  
% 3.52/0.98  fof(f99,plain,(
% 3.52/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.52/0.98    inference(equality_resolution,[],[f93])).
% 3.52/0.98  
% 3.52/0.98  fof(f87,plain,(
% 3.52/0.98    k1_subset_1(sK5) != sK6 | ~r1_tarski(sK6,k3_subset_1(sK5,sK6))),
% 3.52/0.98    inference(cnf_transformation,[],[f51])).
% 3.52/0.98  
% 3.52/0.98  fof(f96,plain,(
% 3.52/0.98    k1_xboole_0 != sK6 | ~r1_tarski(sK6,k3_subset_1(sK5,sK6))),
% 3.52/0.98    inference(definition_unfolding,[],[f87,f82])).
% 3.52/0.98  
% 3.52/0.98  cnf(c_13,plain,
% 3.52/0.98      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 3.52/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1568,plain,
% 3.52/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_16,plain,
% 3.52/0.98      ( r1_tarski(X0,X0) ),
% 3.52/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1566,plain,
% 3.52/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_32,negated_conjecture,
% 3.52/0.98      ( r1_tarski(sK6,k3_subset_1(sK5,sK6)) | k1_xboole_0 = sK6 ),
% 3.52/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1557,plain,
% 3.52/0.98      ( k1_xboole_0 = sK6
% 3.52/0.98      | r1_tarski(sK6,k3_subset_1(sK5,sK6)) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_29,plain,
% 3.52/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/0.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.52/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_33,negated_conjecture,
% 3.52/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
% 3.52/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_584,plain,
% 3.52/0.98      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.52/0.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5)
% 3.52/0.98      | sK6 != X1 ),
% 3.52/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_585,plain,
% 3.52/0.98      ( k3_subset_1(X0,sK6) = k4_xboole_0(X0,sK6)
% 3.52/0.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5) ),
% 3.52/0.98      inference(unflattening,[status(thm)],[c_584]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1649,plain,
% 3.52/0.98      ( k3_subset_1(sK5,sK6) = k4_xboole_0(sK5,sK6) ),
% 3.52/0.98      inference(equality_resolution,[status(thm)],[c_585]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1795,plain,
% 3.52/0.98      ( sK6 = k1_xboole_0
% 3.52/0.98      | r1_tarski(sK6,k4_xboole_0(sK5,sK6)) = iProver_top ),
% 3.52/0.98      inference(light_normalisation,[status(thm)],[c_1557,c_1649]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_19,plain,
% 3.52/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.52/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_261,plain,
% 3.52/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.52/0.98      inference(prop_impl,[status(thm)],[c_19]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_20,plain,
% 3.52/0.98      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 3.52/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_503,plain,
% 3.52/0.98      ( ~ r1_tarski(X0,X1)
% 3.52/0.98      | X0 != X2
% 3.52/0.98      | k4_xboole_0(X3,X1) != X4
% 3.52/0.98      | k4_xboole_0(X2,X4) = X2 ),
% 3.52/0.98      inference(resolution_lifted,[status(thm)],[c_261,c_20]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_504,plain,
% 3.52/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0 ),
% 3.52/0.98      inference(unflattening,[status(thm)],[c_503]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1556,plain,
% 3.52/0.98      ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
% 3.52/0.98      | r1_tarski(X0,X2) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2595,plain,
% 3.52/0.98      ( k4_xboole_0(sK6,k4_xboole_0(X0,k4_xboole_0(sK5,sK6))) = sK6
% 3.52/0.98      | sK6 = k1_xboole_0 ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_1795,c_1556]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1563,plain,
% 3.52/0.98      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 3.52/0.98      | r1_tarski(X0,X2) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2863,plain,
% 3.52/0.98      ( sK6 = k1_xboole_0
% 3.52/0.98      | r1_xboole_0(X0,sK6) = iProver_top
% 3.52/0.98      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(sK5,sK6))) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2595,c_1563]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2971,plain,
% 3.52/0.98      ( sK6 = k1_xboole_0
% 3.52/0.98      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK5,sK6)),sK6) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_1566,c_2863]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_78,plain,
% 3.52/0.98      ( r1_tarski(sK6,sK6) ),
% 3.52/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_14,plain,
% 3.52/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.52/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_82,plain,
% 3.52/0.98      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 3.52/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_85,plain,
% 3.52/0.98      ( r2_hidden(sK3(sK6),sK6) | k1_xboole_0 = sK6 ),
% 3.52/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_10,plain,
% 3.52/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 3.52/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1701,plain,
% 3.52/0.98      ( ~ r1_xboole_0(sK6,X0)
% 3.52/0.98      | ~ r2_hidden(sK3(sK6),X0)
% 3.52/0.98      | ~ r2_hidden(sK3(sK6),sK6) ),
% 3.52/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1703,plain,
% 3.52/0.98      ( ~ r1_xboole_0(sK6,sK6) | ~ r2_hidden(sK3(sK6),sK6) ),
% 3.52/0.98      inference(instantiation,[status(thm)],[c_1701]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_28,plain,
% 3.52/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_571,plain,
% 3.52/0.98      ( r2_hidden(X0,X1)
% 3.52/0.98      | v1_xboole_0(X1)
% 3.52/0.98      | k1_zfmisc_1(sK5) != X1
% 3.52/0.98      | sK6 != X0 ),
% 3.52/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_33]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_572,plain,
% 3.52/0.98      ( r2_hidden(sK6,k1_zfmisc_1(sK5)) | v1_xboole_0(k1_zfmisc_1(sK5)) ),
% 3.52/0.98      inference(unflattening,[status(thm)],[c_571]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_30,plain,
% 3.52/0.98      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.52/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_578,plain,
% 3.52/0.98      ( r2_hidden(sK6,k1_zfmisc_1(sK5)) ),
% 3.52/0.98      inference(forward_subsumption_resolution,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_572,c_30]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1555,plain,
% 3.52/0.98      ( r2_hidden(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_24,plain,
% 3.52/0.98      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1559,plain,
% 3.52/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.52/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2301,plain,
% 3.52/0.98      ( r1_tarski(sK6,sK5) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_1555,c_1559]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2305,plain,
% 3.52/0.98      ( r1_tarski(sK6,sK5) ),
% 3.52/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2301]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_948,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2623,plain,
% 3.52/0.98      ( sK6 != X0 | sK6 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.52/0.98      inference(instantiation,[status(thm)],[c_948]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2624,plain,
% 3.52/0.98      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 3.52/0.98      inference(instantiation,[status(thm)],[c_2623]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_0,plain,
% 3.52/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2628,plain,
% 3.52/0.98      ( k4_xboole_0(sK6,k4_xboole_0(sK5,sK6)) = k5_xboole_0(sK6,sK6)
% 3.52/0.98      | sK6 = k1_xboole_0 ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2595,c_0]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2593,plain,
% 3.52/0.98      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_1566,c_1556]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2629,plain,
% 3.52/0.98      ( k5_xboole_0(sK6,sK6) = sK6 | sK6 = k1_xboole_0 ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_2628,c_2593]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2594,plain,
% 3.52/0.98      ( k4_xboole_0(sK6,k4_xboole_0(X0,sK5)) = sK6 ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2301,c_1556]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3022,plain,
% 3.52/0.98      ( k5_xboole_0(sK6,sK6) = k4_xboole_0(sK6,sK5) ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2594,c_0]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3031,plain,
% 3.52/0.98      ( k4_xboole_0(sK6,sK5) = sK6 | sK6 = k1_xboole_0 ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_2629,c_3022]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3034,plain,
% 3.52/0.98      ( sK6 = k1_xboole_0
% 3.52/0.98      | r1_xboole_0(X0,sK6) = iProver_top
% 3.52/0.98      | r1_tarski(X0,sK5) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_3031,c_1563]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3038,plain,
% 3.52/0.98      ( r1_xboole_0(X0,sK6) | ~ r1_tarski(X0,sK5) | sK6 = k1_xboole_0 ),
% 3.52/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3034]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3040,plain,
% 3.52/0.98      ( r1_xboole_0(sK6,sK6) | ~ r1_tarski(sK6,sK5) | sK6 = k1_xboole_0 ),
% 3.52/0.98      inference(instantiation,[status(thm)],[c_3038]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3122,plain,
% 3.52/0.98      ( sK6 = k1_xboole_0 ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_2971,c_78,c_82,c_85,c_1703,c_2305,c_2624,c_3040]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3125,plain,
% 3.52/0.98      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK5)) = k1_xboole_0 ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_3122,c_2594]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_9,plain,
% 3.52/0.98      ( r2_hidden(X0,X1)
% 3.52/0.98      | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 3.52/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1572,plain,
% 3.52/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.52/0.98      | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4492,plain,
% 3.52/0.98      ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.52/0.98      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_3125,c_1572]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_18,plain,
% 3.52/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.52/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1565,plain,
% 3.52/0.98      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3020,plain,
% 3.52/0.98      ( r1_xboole_0(sK6,k4_xboole_0(X0,sK5)) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2594,c_1565]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4062,plain,
% 3.52/0.98      ( r1_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK5)) = iProver_top ),
% 3.52/0.98      inference(light_normalisation,[status(thm)],[c_3020,c_3122]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1571,plain,
% 3.52/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.52/0.98      | r2_hidden(X2,X1) != iProver_top
% 3.52/0.98      | r2_hidden(X2,X0) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4235,plain,
% 3.52/0.98      ( r2_hidden(X0,k4_xboole_0(X1,sK5)) != iProver_top
% 3.52/0.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_4062,c_1571]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_8,plain,
% 3.52/0.98      ( r2_hidden(X0,X1)
% 3.52/0.98      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 3.52/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1573,plain,
% 3.52/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.52/0.98      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4489,plain,
% 3.52/0.98      ( r2_hidden(X0,k4_xboole_0(X1,sK5)) = iProver_top
% 3.52/0.98      | r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_3125,c_1573]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4678,plain,
% 3.52/0.98      ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_4492,c_4235,c_4489]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4689,plain,
% 3.52/0.98      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_1568,c_4678]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3021,plain,
% 3.52/0.98      ( k4_xboole_0(sK6,k4_xboole_0(X0,sK5)) = k5_xboole_0(sK6,k4_xboole_0(sK6,sK6)) ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2594,c_0]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3024,plain,
% 3.52/0.98      ( k5_xboole_0(sK6,k4_xboole_0(sK6,sK6)) = sK6 ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_3021,c_2594]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4172,plain,
% 3.52/0.98      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 3.52/0.98      inference(light_normalisation,[status(thm)],[c_3024,c_3024,c_3122]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4848,plain,
% 3.52/0.98      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_4689,c_4172]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3481,plain,
% 3.52/0.98      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK5) ),
% 3.52/0.98      inference(light_normalisation,[status(thm)],[c_3022,c_3022,c_3122]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5103,plain,
% 3.52/0.98      ( k4_xboole_0(k1_xboole_0,sK5) = k1_xboole_0 ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_4848,c_3481]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5413,plain,
% 3.52/0.98      ( k4_xboole_0(sK5,k1_xboole_0) = sK5 ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_5103,c_2593]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_31,negated_conjecture,
% 3.52/0.98      ( ~ r1_tarski(sK6,k3_subset_1(sK5,sK6)) | k1_xboole_0 != sK6 ),
% 3.52/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1558,plain,
% 3.52/0.98      ( k1_xboole_0 != sK6
% 3.52/0.98      | r1_tarski(sK6,k3_subset_1(sK5,sK6)) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1797,plain,
% 3.52/0.98      ( sK6 != k1_xboole_0
% 3.52/0.98      | r1_tarski(sK6,k4_xboole_0(sK5,sK6)) != iProver_top ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_1649,c_1558]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3131,plain,
% 3.52/0.98      ( k1_xboole_0 != k1_xboole_0
% 3.52/0.98      | r1_tarski(k1_xboole_0,k4_xboole_0(sK5,k1_xboole_0)) != iProver_top ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_3122,c_1797]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3134,plain,
% 3.52/0.98      ( r1_tarski(k1_xboole_0,k4_xboole_0(sK5,k1_xboole_0)) != iProver_top ),
% 3.52/0.98      inference(equality_resolution_simp,[status(thm)],[c_3131]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5709,plain,
% 3.52/0.98      ( r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_5413,c_3134]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3128,plain,
% 3.52/0.98      ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_3122,c_2301]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(contradiction,plain,
% 3.52/0.98      ( $false ),
% 3.52/0.98      inference(minisat,[status(thm)],[c_5709,c_3128]) ).
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  ------                               Statistics
% 3.52/0.98  
% 3.52/0.98  ------ General
% 3.52/0.98  
% 3.52/0.98  abstr_ref_over_cycles:                  0
% 3.52/0.98  abstr_ref_under_cycles:                 0
% 3.52/0.98  gc_basic_clause_elim:                   0
% 3.52/0.98  forced_gc_time:                         0
% 3.52/0.98  parsing_time:                           0.012
% 3.52/0.98  unif_index_cands_time:                  0.
% 3.52/0.98  unif_index_add_time:                    0.
% 3.52/0.98  orderings_time:                         0.
% 3.52/0.98  out_proof_time:                         0.012
% 3.52/0.98  total_time:                             0.221
% 3.52/0.98  num_of_symbols:                         48
% 3.52/0.98  num_of_terms:                           5395
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing
% 3.52/0.98  
% 3.52/0.98  num_of_splits:                          0
% 3.52/0.98  num_of_split_atoms:                     0
% 3.52/0.98  num_of_reused_defs:                     0
% 3.52/0.98  num_eq_ax_congr_red:                    39
% 3.52/0.98  num_of_sem_filtered_clauses:            1
% 3.52/0.98  num_of_subtypes:                        0
% 3.52/0.98  monotx_restored_types:                  0
% 3.52/0.98  sat_num_of_epr_types:                   0
% 3.52/0.98  sat_num_of_non_cyclic_types:            0
% 3.52/0.98  sat_guarded_non_collapsed_types:        0
% 3.52/0.98  num_pure_diseq_elim:                    0
% 3.52/0.98  simp_replaced_by:                       0
% 3.52/0.98  res_preprocessed:                       139
% 3.52/0.98  prep_upred:                             0
% 3.52/0.98  prep_unflattend:                        17
% 3.52/0.98  smt_new_axioms:                         0
% 3.52/0.98  pred_elim_cands:                        3
% 3.52/0.98  pred_elim:                              2
% 3.52/0.98  pred_elim_cl:                           4
% 3.52/0.98  pred_elim_cycles:                       5
% 3.52/0.98  merged_defs:                            24
% 3.52/0.98  merged_defs_ncl:                        0
% 3.52/0.98  bin_hyper_res:                          25
% 3.52/0.98  prep_cycles:                            4
% 3.52/0.98  pred_elim_time:                         0.006
% 3.52/0.98  splitting_time:                         0.
% 3.52/0.98  sem_filter_time:                        0.
% 3.52/0.98  monotx_time:                            0.001
% 3.52/0.98  subtype_inf_time:                       0.
% 3.52/0.98  
% 3.52/0.98  ------ Problem properties
% 3.52/0.98  
% 3.52/0.98  clauses:                                29
% 3.52/0.98  conjectures:                            2
% 3.52/0.98  epr:                                    4
% 3.52/0.98  horn:                                   21
% 3.52/0.98  ground:                                 3
% 3.52/0.98  unary:                                  3
% 3.52/0.98  binary:                                 17
% 3.52/0.98  lits:                                   65
% 3.52/0.98  lits_eq:                                16
% 3.52/0.98  fd_pure:                                0
% 3.52/0.98  fd_pseudo:                              0
% 3.52/0.98  fd_cond:                                1
% 3.52/0.98  fd_pseudo_cond:                         6
% 3.52/0.98  ac_symbols:                             0
% 3.52/0.98  
% 3.52/0.98  ------ Propositional Solver
% 3.52/0.98  
% 3.52/0.98  prop_solver_calls:                      28
% 3.52/0.98  prop_fast_solver_calls:                 844
% 3.52/0.98  smt_solver_calls:                       0
% 3.52/0.98  smt_fast_solver_calls:                  0
% 3.52/0.98  prop_num_of_clauses:                    2492
% 3.52/0.98  prop_preprocess_simplified:             8294
% 3.52/0.98  prop_fo_subsumed:                       12
% 3.52/0.98  prop_solver_time:                       0.
% 3.52/0.98  smt_solver_time:                        0.
% 3.52/0.98  smt_fast_solver_time:                   0.
% 3.52/0.98  prop_fast_solver_time:                  0.
% 3.52/0.98  prop_unsat_core_time:                   0.
% 3.52/0.98  
% 3.52/0.98  ------ QBF
% 3.52/0.98  
% 3.52/0.98  qbf_q_res:                              0
% 3.52/0.98  qbf_num_tautologies:                    0
% 3.52/0.98  qbf_prep_cycles:                        0
% 3.52/0.98  
% 3.52/0.98  ------ BMC1
% 3.52/0.98  
% 3.52/0.98  bmc1_current_bound:                     -1
% 3.52/0.98  bmc1_last_solved_bound:                 -1
% 3.52/0.98  bmc1_unsat_core_size:                   -1
% 3.52/0.98  bmc1_unsat_core_parents_size:           -1
% 3.52/0.98  bmc1_merge_next_fun:                    0
% 3.52/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.52/0.98  
% 3.52/0.98  ------ Instantiation
% 3.52/0.98  
% 3.52/0.98  inst_num_of_clauses:                    697
% 3.52/0.98  inst_num_in_passive:                    119
% 3.52/0.98  inst_num_in_active:                     271
% 3.52/0.98  inst_num_in_unprocessed:                307
% 3.52/0.98  inst_num_of_loops:                      340
% 3.52/0.98  inst_num_of_learning_restarts:          0
% 3.52/0.98  inst_num_moves_active_passive:          69
% 3.52/0.98  inst_lit_activity:                      0
% 3.52/0.98  inst_lit_activity_moves:                0
% 3.52/0.98  inst_num_tautologies:                   0
% 3.52/0.98  inst_num_prop_implied:                  0
% 3.52/0.98  inst_num_existing_simplified:           0
% 3.52/0.98  inst_num_eq_res_simplified:             0
% 3.52/0.98  inst_num_child_elim:                    0
% 3.52/0.98  inst_num_of_dismatching_blockings:      190
% 3.52/0.98  inst_num_of_non_proper_insts:           560
% 3.52/0.98  inst_num_of_duplicates:                 0
% 3.52/0.98  inst_inst_num_from_inst_to_res:         0
% 3.52/0.98  inst_dismatching_checking_time:         0.
% 3.52/0.98  
% 3.52/0.98  ------ Resolution
% 3.52/0.98  
% 3.52/0.98  res_num_of_clauses:                     0
% 3.52/0.98  res_num_in_passive:                     0
% 3.52/0.98  res_num_in_active:                      0
% 3.52/0.98  res_num_of_loops:                       143
% 3.52/0.98  res_forward_subset_subsumed:            26
% 3.52/0.98  res_backward_subset_subsumed:           0
% 3.52/0.98  res_forward_subsumed:                   2
% 3.52/0.98  res_backward_subsumed:                  1
% 3.52/0.98  res_forward_subsumption_resolution:     2
% 3.52/0.98  res_backward_subsumption_resolution:    0
% 3.52/0.98  res_clause_to_clause_subsumption:       495
% 3.52/0.98  res_orphan_elimination:                 0
% 3.52/0.98  res_tautology_del:                      75
% 3.52/0.98  res_num_eq_res_simplified:              0
% 3.52/0.98  res_num_sel_changes:                    0
% 3.52/0.98  res_moves_from_active_to_pass:          0
% 3.52/0.98  
% 3.52/0.98  ------ Superposition
% 3.52/0.98  
% 3.52/0.98  sup_time_total:                         0.
% 3.52/0.98  sup_time_generating:                    0.
% 3.52/0.98  sup_time_sim_full:                      0.
% 3.52/0.98  sup_time_sim_immed:                     0.
% 3.52/0.98  
% 3.52/0.98  sup_num_of_clauses:                     130
% 3.52/0.98  sup_num_in_active:                      47
% 3.52/0.98  sup_num_in_passive:                     83
% 3.52/0.98  sup_num_of_loops:                       67
% 3.52/0.98  sup_fw_superposition:                   69
% 3.52/0.98  sup_bw_superposition:                   114
% 3.52/0.98  sup_immediate_simplified:               27
% 3.52/0.98  sup_given_eliminated:                   1
% 3.52/0.98  comparisons_done:                       0
% 3.52/0.98  comparisons_avoided:                    8
% 3.52/0.98  
% 3.52/0.98  ------ Simplifications
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  sim_fw_subset_subsumed:                 7
% 3.52/0.98  sim_bw_subset_subsumed:                 13
% 3.52/0.98  sim_fw_subsumed:                        2
% 3.52/0.98  sim_bw_subsumed:                        0
% 3.52/0.98  sim_fw_subsumption_res:                 0
% 3.52/0.98  sim_bw_subsumption_res:                 0
% 3.52/0.98  sim_tautology_del:                      12
% 3.52/0.98  sim_eq_tautology_del:                   8
% 3.52/0.98  sim_eq_res_simp:                        3
% 3.52/0.98  sim_fw_demodulated:                     9
% 3.52/0.98  sim_bw_demodulated:                     17
% 3.52/0.98  sim_light_normalised:                   15
% 3.52/0.98  sim_joinable_taut:                      0
% 3.52/0.98  sim_joinable_simp:                      0
% 3.52/0.98  sim_ac_normalised:                      0
% 3.52/0.98  sim_smt_subsumption:                    0
% 3.52/0.98  
%------------------------------------------------------------------------------
