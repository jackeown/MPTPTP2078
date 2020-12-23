%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:57 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 512 expanded)
%              Number of clauses        :   67 ( 154 expanded)
%              Number of leaves         :   18 ( 125 expanded)
%              Depth                    :   19
%              Number of atoms          :  384 (1645 expanded)
%              Number of equality atoms :  147 ( 589 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f33])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f24,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,
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

fof(f43,plain,
    ( ( k1_subset_1(sK4) != sK5
      | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
    & ( k1_subset_1(sK4) = sK5
      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f41,f42])).

fof(f74,plain,
    ( k1_subset_1(sK4) = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f86,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(definition_unfolding,[],[f74,f70])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f60,f56,f56])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f56])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f75,plain,
    ( k1_subset_1(sK4) != sK5
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,
    ( k1_xboole_0 != sK5
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(definition_unfolding,[],[f75,f70])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f59,f56])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f63])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1743,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1735,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1742,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3987,plain,
    ( k3_xboole_0(sK5,k3_subset_1(sK4,sK5)) = sK5
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1735,c_1742])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1751,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15838,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k3_subset_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,k5_xboole_0(sK5,sK5)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3987,c_1751])).

cnf(c_14,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2166,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_0])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2174,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2166,c_14,c_16])).

cnf(c_3008,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2174,c_0])).

cnf(c_3011,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3008,c_14,c_16])).

cnf(c_3012,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3011,c_2174])).

cnf(c_15881,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k3_subset_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15838,c_3012])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_485,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_486,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK5)) = k3_subset_1(X0,sK5)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_1918,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k3_subset_1(sK4,sK5) ),
    inference(equality_resolution,[status(thm)],[c_486])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1750,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7328,plain,
    ( r2_hidden(X0,k3_subset_1(sK4,sK5)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1918,c_1750])).

cnf(c_7341,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1750])).

cnf(c_7389,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7341,c_16])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1749,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5237,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1749])).

cnf(c_7030,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_5237])).

cnf(c_8314,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7389,c_7030])).

cnf(c_16583,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15881,c_7030,c_7389,c_7328])).

cnf(c_16584,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_16583])).

cnf(c_16593,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1743,c_16584])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_472,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_473,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_479,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_473,c_26])).

cnf(c_1734,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_20,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1737,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2824,plain,
    ( r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1737])).

cnf(c_17787,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16593,c_2824])).

cnf(c_27,negated_conjecture,
    ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1736,plain,
    ( k1_xboole_0 != sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17799,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k3_subset_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16593,c_1736])).

cnf(c_17800,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17799])).

cnf(c_15,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1741,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2168,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1741])).

cnf(c_2235,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_2168])).

cnf(c_23,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_452,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_453,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_463,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_453,c_26])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_778,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_835,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_463,c_778])).

cnf(c_1733,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_2346,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2235,c_1733])).

cnf(c_2347,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2346,c_14,c_16])).

cnf(c_17802,plain,
    ( r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17800,c_2347])).

cnf(c_17820,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17787,c_17802])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.99  
% 3.53/0.99  ------  iProver source info
% 3.53/0.99  
% 3.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.99  git: non_committed_changes: false
% 3.53/0.99  git: last_make_outside_of_git: false
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options
% 3.53/0.99  
% 3.53/0.99  --out_options                           all
% 3.53/0.99  --tptp_safe_out                         true
% 3.53/0.99  --problem_path                          ""
% 3.53/0.99  --include_path                          ""
% 3.53/0.99  --clausifier                            res/vclausify_rel
% 3.53/0.99  --clausifier_options                    --mode clausify
% 3.53/0.99  --stdin                                 false
% 3.53/0.99  --stats_out                             all
% 3.53/0.99  
% 3.53/0.99  ------ General Options
% 3.53/0.99  
% 3.53/0.99  --fof                                   false
% 3.53/0.99  --time_out_real                         305.
% 3.53/0.99  --time_out_virtual                      -1.
% 3.53/0.99  --symbol_type_check                     false
% 3.53/0.99  --clausify_out                          false
% 3.53/0.99  --sig_cnt_out                           false
% 3.53/0.99  --trig_cnt_out                          false
% 3.53/0.99  --trig_cnt_out_tolerance                1.
% 3.53/0.99  --trig_cnt_out_sk_spl                   false
% 3.53/0.99  --abstr_cl_out                          false
% 3.53/0.99  
% 3.53/0.99  ------ Global Options
% 3.53/0.99  
% 3.53/0.99  --schedule                              default
% 3.53/0.99  --add_important_lit                     false
% 3.53/0.99  --prop_solver_per_cl                    1000
% 3.53/0.99  --min_unsat_core                        false
% 3.53/0.99  --soft_assumptions                      false
% 3.53/0.99  --soft_lemma_size                       3
% 3.53/0.99  --prop_impl_unit_size                   0
% 3.53/0.99  --prop_impl_unit                        []
% 3.53/0.99  --share_sel_clauses                     true
% 3.53/0.99  --reset_solvers                         false
% 3.53/0.99  --bc_imp_inh                            [conj_cone]
% 3.53/0.99  --conj_cone_tolerance                   3.
% 3.53/0.99  --extra_neg_conj                        none
% 3.53/0.99  --large_theory_mode                     true
% 3.53/0.99  --prolific_symb_bound                   200
% 3.53/0.99  --lt_threshold                          2000
% 3.53/0.99  --clause_weak_htbl                      true
% 3.53/0.99  --gc_record_bc_elim                     false
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing Options
% 3.53/0.99  
% 3.53/0.99  --preprocessing_flag                    true
% 3.53/0.99  --time_out_prep_mult                    0.1
% 3.53/0.99  --splitting_mode                        input
% 3.53/0.99  --splitting_grd                         true
% 3.53/0.99  --splitting_cvd                         false
% 3.53/0.99  --splitting_cvd_svl                     false
% 3.53/0.99  --splitting_nvd                         32
% 3.53/0.99  --sub_typing                            true
% 3.53/0.99  --prep_gs_sim                           true
% 3.53/0.99  --prep_unflatten                        true
% 3.53/0.99  --prep_res_sim                          true
% 3.53/0.99  --prep_upred                            true
% 3.53/0.99  --prep_sem_filter                       exhaustive
% 3.53/0.99  --prep_sem_filter_out                   false
% 3.53/0.99  --pred_elim                             true
% 3.53/0.99  --res_sim_input                         true
% 3.53/0.99  --eq_ax_congr_red                       true
% 3.53/0.99  --pure_diseq_elim                       true
% 3.53/0.99  --brand_transform                       false
% 3.53/0.99  --non_eq_to_eq                          false
% 3.53/0.99  --prep_def_merge                        true
% 3.53/0.99  --prep_def_merge_prop_impl              false
% 3.53/0.99  --prep_def_merge_mbd                    true
% 3.53/0.99  --prep_def_merge_tr_red                 false
% 3.53/0.99  --prep_def_merge_tr_cl                  false
% 3.53/0.99  --smt_preprocessing                     true
% 3.53/0.99  --smt_ac_axioms                         fast
% 3.53/0.99  --preprocessed_out                      false
% 3.53/0.99  --preprocessed_stats                    false
% 3.53/0.99  
% 3.53/0.99  ------ Abstraction refinement Options
% 3.53/0.99  
% 3.53/0.99  --abstr_ref                             []
% 3.53/0.99  --abstr_ref_prep                        false
% 3.53/0.99  --abstr_ref_until_sat                   false
% 3.53/0.99  --abstr_ref_sig_restrict                funpre
% 3.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.99  --abstr_ref_under                       []
% 3.53/0.99  
% 3.53/0.99  ------ SAT Options
% 3.53/0.99  
% 3.53/0.99  --sat_mode                              false
% 3.53/0.99  --sat_fm_restart_options                ""
% 3.53/0.99  --sat_gr_def                            false
% 3.53/0.99  --sat_epr_types                         true
% 3.53/0.99  --sat_non_cyclic_types                  false
% 3.53/0.99  --sat_finite_models                     false
% 3.53/0.99  --sat_fm_lemmas                         false
% 3.53/0.99  --sat_fm_prep                           false
% 3.53/0.99  --sat_fm_uc_incr                        true
% 3.53/0.99  --sat_out_model                         small
% 3.53/0.99  --sat_out_clauses                       false
% 3.53/0.99  
% 3.53/0.99  ------ QBF Options
% 3.53/0.99  
% 3.53/0.99  --qbf_mode                              false
% 3.53/0.99  --qbf_elim_univ                         false
% 3.53/0.99  --qbf_dom_inst                          none
% 3.53/0.99  --qbf_dom_pre_inst                      false
% 3.53/0.99  --qbf_sk_in                             false
% 3.53/0.99  --qbf_pred_elim                         true
% 3.53/0.99  --qbf_split                             512
% 3.53/0.99  
% 3.53/0.99  ------ BMC1 Options
% 3.53/0.99  
% 3.53/0.99  --bmc1_incremental                      false
% 3.53/0.99  --bmc1_axioms                           reachable_all
% 3.53/0.99  --bmc1_min_bound                        0
% 3.53/0.99  --bmc1_max_bound                        -1
% 3.53/0.99  --bmc1_max_bound_default                -1
% 3.53/0.99  --bmc1_symbol_reachability              true
% 3.53/0.99  --bmc1_property_lemmas                  false
% 3.53/0.99  --bmc1_k_induction                      false
% 3.53/0.99  --bmc1_non_equiv_states                 false
% 3.53/0.99  --bmc1_deadlock                         false
% 3.53/0.99  --bmc1_ucm                              false
% 3.53/0.99  --bmc1_add_unsat_core                   none
% 3.53/0.99  --bmc1_unsat_core_children              false
% 3.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.99  --bmc1_out_stat                         full
% 3.53/0.99  --bmc1_ground_init                      false
% 3.53/0.99  --bmc1_pre_inst_next_state              false
% 3.53/0.99  --bmc1_pre_inst_state                   false
% 3.53/0.99  --bmc1_pre_inst_reach_state             false
% 3.53/0.99  --bmc1_out_unsat_core                   false
% 3.53/0.99  --bmc1_aig_witness_out                  false
% 3.53/0.99  --bmc1_verbose                          false
% 3.53/0.99  --bmc1_dump_clauses_tptp                false
% 3.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.99  --bmc1_dump_file                        -
% 3.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.99  --bmc1_ucm_extend_mode                  1
% 3.53/0.99  --bmc1_ucm_init_mode                    2
% 3.53/0.99  --bmc1_ucm_cone_mode                    none
% 3.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.99  --bmc1_ucm_relax_model                  4
% 3.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.99  --bmc1_ucm_layered_model                none
% 3.53/0.99  --bmc1_ucm_max_lemma_size               10
% 3.53/0.99  
% 3.53/0.99  ------ AIG Options
% 3.53/0.99  
% 3.53/0.99  --aig_mode                              false
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation Options
% 3.53/0.99  
% 3.53/0.99  --instantiation_flag                    true
% 3.53/0.99  --inst_sos_flag                         false
% 3.53/0.99  --inst_sos_phase                        true
% 3.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel_side                     num_symb
% 3.53/0.99  --inst_solver_per_active                1400
% 3.53/0.99  --inst_solver_calls_frac                1.
% 3.53/0.99  --inst_passive_queue_type               priority_queues
% 3.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.99  --inst_passive_queues_freq              [25;2]
% 3.53/0.99  --inst_dismatching                      true
% 3.53/0.99  --inst_eager_unprocessed_to_passive     true
% 3.53/0.99  --inst_prop_sim_given                   true
% 3.53/0.99  --inst_prop_sim_new                     false
% 3.53/0.99  --inst_subs_new                         false
% 3.53/0.99  --inst_eq_res_simp                      false
% 3.53/0.99  --inst_subs_given                       false
% 3.53/0.99  --inst_orphan_elimination               true
% 3.53/0.99  --inst_learning_loop_flag               true
% 3.53/0.99  --inst_learning_start                   3000
% 3.53/0.99  --inst_learning_factor                  2
% 3.53/0.99  --inst_start_prop_sim_after_learn       3
% 3.53/0.99  --inst_sel_renew                        solver
% 3.53/0.99  --inst_lit_activity_flag                true
% 3.53/0.99  --inst_restr_to_given                   false
% 3.53/0.99  --inst_activity_threshold               500
% 3.53/0.99  --inst_out_proof                        true
% 3.53/0.99  
% 3.53/0.99  ------ Resolution Options
% 3.53/0.99  
% 3.53/0.99  --resolution_flag                       true
% 3.53/0.99  --res_lit_sel                           adaptive
% 3.53/0.99  --res_lit_sel_side                      none
% 3.53/0.99  --res_ordering                          kbo
% 3.53/0.99  --res_to_prop_solver                    active
% 3.53/0.99  --res_prop_simpl_new                    false
% 3.53/0.99  --res_prop_simpl_given                  true
% 3.53/0.99  --res_passive_queue_type                priority_queues
% 3.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.99  --res_passive_queues_freq               [15;5]
% 3.53/0.99  --res_forward_subs                      full
% 3.53/0.99  --res_backward_subs                     full
% 3.53/0.99  --res_forward_subs_resolution           true
% 3.53/0.99  --res_backward_subs_resolution          true
% 3.53/0.99  --res_orphan_elimination                true
% 3.53/0.99  --res_time_limit                        2.
% 3.53/0.99  --res_out_proof                         true
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Options
% 3.53/0.99  
% 3.53/0.99  --superposition_flag                    true
% 3.53/0.99  --sup_passive_queue_type                priority_queues
% 3.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.99  --demod_completeness_check              fast
% 3.53/0.99  --demod_use_ground                      true
% 3.53/0.99  --sup_to_prop_solver                    passive
% 3.53/0.99  --sup_prop_simpl_new                    true
% 3.53/0.99  --sup_prop_simpl_given                  true
% 3.53/0.99  --sup_fun_splitting                     false
% 3.53/0.99  --sup_smt_interval                      50000
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Simplification Setup
% 3.53/0.99  
% 3.53/0.99  --sup_indices_passive                   []
% 3.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_full_bw                           [BwDemod]
% 3.53/0.99  --sup_immed_triv                        [TrivRules]
% 3.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_immed_bw_main                     []
% 3.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  
% 3.53/0.99  ------ Combination Options
% 3.53/0.99  
% 3.53/0.99  --comb_res_mult                         3
% 3.53/0.99  --comb_sup_mult                         2
% 3.53/0.99  --comb_inst_mult                        10
% 3.53/0.99  
% 3.53/0.99  ------ Debug Options
% 3.53/0.99  
% 3.53/0.99  --dbg_backtrace                         false
% 3.53/0.99  --dbg_dump_prop_clauses                 false
% 3.53/0.99  --dbg_dump_prop_clauses_file            -
% 3.53/0.99  --dbg_out_stat                          false
% 3.53/0.99  ------ Parsing...
% 3.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.99  ------ Proving...
% 3.53/0.99  ------ Problem Properties 
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  clauses                                 26
% 3.53/0.99  conjectures                             2
% 3.53/1.00  EPR                                     1
% 3.53/1.00  Horn                                    17
% 3.53/1.00  unary                                   5
% 3.53/1.00  binary                                  14
% 3.53/1.00  lits                                    55
% 3.53/1.00  lits eq                                 17
% 3.53/1.00  fd_pure                                 0
% 3.53/1.00  fd_pseudo                               0
% 3.53/1.00  fd_cond                                 1
% 3.53/1.00  fd_pseudo_cond                          5
% 3.53/1.00  AC symbols                              0
% 3.53/1.00  
% 3.53/1.00  ------ Schedule dynamic 5 is on 
% 3.53/1.00  
% 3.53/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ 
% 3.53/1.00  Current options:
% 3.53/1.00  ------ 
% 3.53/1.00  
% 3.53/1.00  ------ Input Options
% 3.53/1.00  
% 3.53/1.00  --out_options                           all
% 3.53/1.00  --tptp_safe_out                         true
% 3.53/1.00  --problem_path                          ""
% 3.53/1.00  --include_path                          ""
% 3.53/1.00  --clausifier                            res/vclausify_rel
% 3.53/1.00  --clausifier_options                    --mode clausify
% 3.53/1.00  --stdin                                 false
% 3.53/1.00  --stats_out                             all
% 3.53/1.00  
% 3.53/1.00  ------ General Options
% 3.53/1.00  
% 3.53/1.00  --fof                                   false
% 3.53/1.00  --time_out_real                         305.
% 3.53/1.00  --time_out_virtual                      -1.
% 3.53/1.00  --symbol_type_check                     false
% 3.53/1.00  --clausify_out                          false
% 3.53/1.00  --sig_cnt_out                           false
% 3.53/1.00  --trig_cnt_out                          false
% 3.53/1.00  --trig_cnt_out_tolerance                1.
% 3.53/1.00  --trig_cnt_out_sk_spl                   false
% 3.53/1.00  --abstr_cl_out                          false
% 3.53/1.00  
% 3.53/1.00  ------ Global Options
% 3.53/1.00  
% 3.53/1.00  --schedule                              default
% 3.53/1.00  --add_important_lit                     false
% 3.53/1.00  --prop_solver_per_cl                    1000
% 3.53/1.00  --min_unsat_core                        false
% 3.53/1.00  --soft_assumptions                      false
% 3.53/1.00  --soft_lemma_size                       3
% 3.53/1.00  --prop_impl_unit_size                   0
% 3.53/1.00  --prop_impl_unit                        []
% 3.53/1.00  --share_sel_clauses                     true
% 3.53/1.00  --reset_solvers                         false
% 3.53/1.00  --bc_imp_inh                            [conj_cone]
% 3.53/1.00  --conj_cone_tolerance                   3.
% 3.53/1.00  --extra_neg_conj                        none
% 3.53/1.00  --large_theory_mode                     true
% 3.53/1.00  --prolific_symb_bound                   200
% 3.53/1.00  --lt_threshold                          2000
% 3.53/1.00  --clause_weak_htbl                      true
% 3.53/1.00  --gc_record_bc_elim                     false
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing Options
% 3.53/1.00  
% 3.53/1.00  --preprocessing_flag                    true
% 3.53/1.00  --time_out_prep_mult                    0.1
% 3.53/1.00  --splitting_mode                        input
% 3.53/1.00  --splitting_grd                         true
% 3.53/1.00  --splitting_cvd                         false
% 3.53/1.00  --splitting_cvd_svl                     false
% 3.53/1.00  --splitting_nvd                         32
% 3.53/1.00  --sub_typing                            true
% 3.53/1.00  --prep_gs_sim                           true
% 3.53/1.00  --prep_unflatten                        true
% 3.53/1.00  --prep_res_sim                          true
% 3.53/1.00  --prep_upred                            true
% 3.53/1.00  --prep_sem_filter                       exhaustive
% 3.53/1.00  --prep_sem_filter_out                   false
% 3.53/1.00  --pred_elim                             true
% 3.53/1.00  --res_sim_input                         true
% 3.53/1.00  --eq_ax_congr_red                       true
% 3.53/1.00  --pure_diseq_elim                       true
% 3.53/1.00  --brand_transform                       false
% 3.53/1.00  --non_eq_to_eq                          false
% 3.53/1.00  --prep_def_merge                        true
% 3.53/1.00  --prep_def_merge_prop_impl              false
% 3.53/1.00  --prep_def_merge_mbd                    true
% 3.53/1.00  --prep_def_merge_tr_red                 false
% 3.53/1.00  --prep_def_merge_tr_cl                  false
% 3.53/1.00  --smt_preprocessing                     true
% 3.53/1.00  --smt_ac_axioms                         fast
% 3.53/1.00  --preprocessed_out                      false
% 3.53/1.00  --preprocessed_stats                    false
% 3.53/1.00  
% 3.53/1.00  ------ Abstraction refinement Options
% 3.53/1.00  
% 3.53/1.00  --abstr_ref                             []
% 3.53/1.00  --abstr_ref_prep                        false
% 3.53/1.00  --abstr_ref_until_sat                   false
% 3.53/1.00  --abstr_ref_sig_restrict                funpre
% 3.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.00  --abstr_ref_under                       []
% 3.53/1.00  
% 3.53/1.00  ------ SAT Options
% 3.53/1.00  
% 3.53/1.00  --sat_mode                              false
% 3.53/1.00  --sat_fm_restart_options                ""
% 3.53/1.00  --sat_gr_def                            false
% 3.53/1.00  --sat_epr_types                         true
% 3.53/1.00  --sat_non_cyclic_types                  false
% 3.53/1.00  --sat_finite_models                     false
% 3.53/1.00  --sat_fm_lemmas                         false
% 3.53/1.00  --sat_fm_prep                           false
% 3.53/1.00  --sat_fm_uc_incr                        true
% 3.53/1.00  --sat_out_model                         small
% 3.53/1.00  --sat_out_clauses                       false
% 3.53/1.00  
% 3.53/1.00  ------ QBF Options
% 3.53/1.00  
% 3.53/1.00  --qbf_mode                              false
% 3.53/1.00  --qbf_elim_univ                         false
% 3.53/1.00  --qbf_dom_inst                          none
% 3.53/1.00  --qbf_dom_pre_inst                      false
% 3.53/1.00  --qbf_sk_in                             false
% 3.53/1.00  --qbf_pred_elim                         true
% 3.53/1.00  --qbf_split                             512
% 3.53/1.00  
% 3.53/1.00  ------ BMC1 Options
% 3.53/1.00  
% 3.53/1.00  --bmc1_incremental                      false
% 3.53/1.00  --bmc1_axioms                           reachable_all
% 3.53/1.00  --bmc1_min_bound                        0
% 3.53/1.00  --bmc1_max_bound                        -1
% 3.53/1.00  --bmc1_max_bound_default                -1
% 3.53/1.00  --bmc1_symbol_reachability              true
% 3.53/1.00  --bmc1_property_lemmas                  false
% 3.53/1.00  --bmc1_k_induction                      false
% 3.53/1.00  --bmc1_non_equiv_states                 false
% 3.53/1.00  --bmc1_deadlock                         false
% 3.53/1.00  --bmc1_ucm                              false
% 3.53/1.00  --bmc1_add_unsat_core                   none
% 3.53/1.00  --bmc1_unsat_core_children              false
% 3.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.00  --bmc1_out_stat                         full
% 3.53/1.00  --bmc1_ground_init                      false
% 3.53/1.00  --bmc1_pre_inst_next_state              false
% 3.53/1.00  --bmc1_pre_inst_state                   false
% 3.53/1.00  --bmc1_pre_inst_reach_state             false
% 3.53/1.00  --bmc1_out_unsat_core                   false
% 3.53/1.00  --bmc1_aig_witness_out                  false
% 3.53/1.00  --bmc1_verbose                          false
% 3.53/1.00  --bmc1_dump_clauses_tptp                false
% 3.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.00  --bmc1_dump_file                        -
% 3.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.00  --bmc1_ucm_extend_mode                  1
% 3.53/1.00  --bmc1_ucm_init_mode                    2
% 3.53/1.00  --bmc1_ucm_cone_mode                    none
% 3.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.00  --bmc1_ucm_relax_model                  4
% 3.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.00  --bmc1_ucm_layered_model                none
% 3.53/1.00  --bmc1_ucm_max_lemma_size               10
% 3.53/1.00  
% 3.53/1.00  ------ AIG Options
% 3.53/1.00  
% 3.53/1.00  --aig_mode                              false
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation Options
% 3.53/1.00  
% 3.53/1.00  --instantiation_flag                    true
% 3.53/1.00  --inst_sos_flag                         false
% 3.53/1.00  --inst_sos_phase                        true
% 3.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel_side                     none
% 3.53/1.00  --inst_solver_per_active                1400
% 3.53/1.00  --inst_solver_calls_frac                1.
% 3.53/1.00  --inst_passive_queue_type               priority_queues
% 3.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.00  --inst_passive_queues_freq              [25;2]
% 3.53/1.00  --inst_dismatching                      true
% 3.53/1.00  --inst_eager_unprocessed_to_passive     true
% 3.53/1.00  --inst_prop_sim_given                   true
% 3.53/1.00  --inst_prop_sim_new                     false
% 3.53/1.00  --inst_subs_new                         false
% 3.53/1.00  --inst_eq_res_simp                      false
% 3.53/1.00  --inst_subs_given                       false
% 3.53/1.00  --inst_orphan_elimination               true
% 3.53/1.00  --inst_learning_loop_flag               true
% 3.53/1.00  --inst_learning_start                   3000
% 3.53/1.00  --inst_learning_factor                  2
% 3.53/1.00  --inst_start_prop_sim_after_learn       3
% 3.53/1.00  --inst_sel_renew                        solver
% 3.53/1.00  --inst_lit_activity_flag                true
% 3.53/1.00  --inst_restr_to_given                   false
% 3.53/1.00  --inst_activity_threshold               500
% 3.53/1.00  --inst_out_proof                        true
% 3.53/1.00  
% 3.53/1.00  ------ Resolution Options
% 3.53/1.00  
% 3.53/1.00  --resolution_flag                       false
% 3.53/1.00  --res_lit_sel                           adaptive
% 3.53/1.00  --res_lit_sel_side                      none
% 3.53/1.00  --res_ordering                          kbo
% 3.53/1.00  --res_to_prop_solver                    active
% 3.53/1.00  --res_prop_simpl_new                    false
% 3.53/1.00  --res_prop_simpl_given                  true
% 3.53/1.00  --res_passive_queue_type                priority_queues
% 3.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.00  --res_passive_queues_freq               [15;5]
% 3.53/1.00  --res_forward_subs                      full
% 3.53/1.00  --res_backward_subs                     full
% 3.53/1.00  --res_forward_subs_resolution           true
% 3.53/1.00  --res_backward_subs_resolution          true
% 3.53/1.00  --res_orphan_elimination                true
% 3.53/1.00  --res_time_limit                        2.
% 3.53/1.00  --res_out_proof                         true
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Options
% 3.53/1.00  
% 3.53/1.00  --superposition_flag                    true
% 3.53/1.00  --sup_passive_queue_type                priority_queues
% 3.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.00  --demod_completeness_check              fast
% 3.53/1.00  --demod_use_ground                      true
% 3.53/1.00  --sup_to_prop_solver                    passive
% 3.53/1.00  --sup_prop_simpl_new                    true
% 3.53/1.00  --sup_prop_simpl_given                  true
% 3.53/1.00  --sup_fun_splitting                     false
% 3.53/1.00  --sup_smt_interval                      50000
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Simplification Setup
% 3.53/1.00  
% 3.53/1.00  --sup_indices_passive                   []
% 3.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_full_bw                           [BwDemod]
% 3.53/1.00  --sup_immed_triv                        [TrivRules]
% 3.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_immed_bw_main                     []
% 3.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.00  
% 3.53/1.00  ------ Combination Options
% 3.53/1.00  
% 3.53/1.00  --comb_res_mult                         3
% 3.53/1.00  --comb_sup_mult                         2
% 3.53/1.00  --comb_inst_mult                        10
% 3.53/1.00  
% 3.53/1.00  ------ Debug Options
% 3.53/1.00  
% 3.53/1.00  --dbg_backtrace                         false
% 3.53/1.00  --dbg_dump_prop_clauses                 false
% 3.53/1.00  --dbg_dump_prop_clauses_file            -
% 3.53/1.00  --dbg_out_stat                          false
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ Proving...
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS status Theorem for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00   Resolution empty clause
% 3.53/1.00  
% 3.53/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  fof(f4,axiom,(
% 3.53/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f20,plain,(
% 3.53/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.53/1.00    inference(ennf_transformation,[],[f4])).
% 3.53/1.00  
% 3.53/1.00  fof(f33,plain,(
% 3.53/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f34,plain,(
% 3.53/1.00    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f33])).
% 3.53/1.00  
% 3.53/1.00  fof(f55,plain,(
% 3.53/1.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.53/1.00    inference(cnf_transformation,[],[f34])).
% 3.53/1.00  
% 3.53/1.00  fof(f16,conjecture,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f17,negated_conjecture,(
% 3.53/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.53/1.00    inference(negated_conjecture,[],[f16])).
% 3.53/1.00  
% 3.53/1.00  fof(f24,plain,(
% 3.53/1.00    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f17])).
% 3.53/1.00  
% 3.53/1.00  fof(f40,plain,(
% 3.53/1.00    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.53/1.00    inference(nnf_transformation,[],[f24])).
% 3.53/1.00  
% 3.53/1.00  fof(f41,plain,(
% 3.53/1.00    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.53/1.00    inference(flattening,[],[f40])).
% 3.53/1.00  
% 3.53/1.00  fof(f42,plain,(
% 3.53/1.00    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))) & (k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f43,plain,(
% 3.53/1.00    (k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))) & (k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f41,f42])).
% 3.53/1.00  
% 3.53/1.00  fof(f74,plain,(
% 3.53/1.00    k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 3.53/1.00    inference(cnf_transformation,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f13,axiom,(
% 3.53/1.00    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f70,plain,(
% 3.53/1.00    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f13])).
% 3.53/1.00  
% 3.53/1.00  fof(f86,plain,(
% 3.53/1.00    k1_xboole_0 = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 3.53/1.00    inference(definition_unfolding,[],[f74,f70])).
% 3.53/1.00  
% 3.53/1.00  fof(f6,axiom,(
% 3.53/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f21,plain,(
% 3.53/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.53/1.00    inference(ennf_transformation,[],[f6])).
% 3.53/1.00  
% 3.53/1.00  fof(f57,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f21])).
% 3.53/1.00  
% 3.53/1.00  fof(f1,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f25,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/1.00    inference(nnf_transformation,[],[f1])).
% 3.53/1.00  
% 3.53/1.00  fof(f26,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/1.00    inference(flattening,[],[f25])).
% 3.53/1.00  
% 3.53/1.00  fof(f27,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/1.00    inference(rectify,[],[f26])).
% 3.53/1.00  
% 3.53/1.00  fof(f28,plain,(
% 3.53/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f29,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.53/1.00  
% 3.53/1.00  fof(f46,plain,(
% 3.53/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.53/1.00    inference(cnf_transformation,[],[f29])).
% 3.53/1.00  
% 3.53/1.00  fof(f5,axiom,(
% 3.53/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f56,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f5])).
% 3.53/1.00  
% 3.53/1.00  fof(f80,plain,(
% 3.53/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.53/1.00    inference(definition_unfolding,[],[f46,f56])).
% 3.53/1.00  
% 3.53/1.00  fof(f87,plain,(
% 3.53/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f80])).
% 3.53/1.00  
% 3.53/1.00  fof(f7,axiom,(
% 3.53/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f58,plain,(
% 3.53/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.53/1.00    inference(cnf_transformation,[],[f7])).
% 3.53/1.00  
% 3.53/1.00  fof(f9,axiom,(
% 3.53/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f60,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f9])).
% 3.53/1.00  
% 3.53/1.00  fof(f76,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.53/1.00    inference(definition_unfolding,[],[f60,f56,f56])).
% 3.53/1.00  
% 3.53/1.00  fof(f10,axiom,(
% 3.53/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f61,plain,(
% 3.53/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.53/1.00    inference(cnf_transformation,[],[f10])).
% 3.53/1.00  
% 3.53/1.00  fof(f14,axiom,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f23,plain,(
% 3.53/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f14])).
% 3.53/1.00  
% 3.53/1.00  fof(f71,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f23])).
% 3.53/1.00  
% 3.53/1.00  fof(f84,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.53/1.00    inference(definition_unfolding,[],[f71,f56])).
% 3.53/1.00  
% 3.53/1.00  fof(f73,plain,(
% 3.53/1.00    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 3.53/1.00    inference(cnf_transformation,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f45,plain,(
% 3.53/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.53/1.00    inference(cnf_transformation,[],[f29])).
% 3.53/1.00  
% 3.53/1.00  fof(f81,plain,(
% 3.53/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.53/1.00    inference(definition_unfolding,[],[f45,f56])).
% 3.53/1.00  
% 3.53/1.00  fof(f88,plain,(
% 3.53/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.53/1.00    inference(equality_resolution,[],[f81])).
% 3.53/1.00  
% 3.53/1.00  fof(f44,plain,(
% 3.53/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.53/1.00    inference(cnf_transformation,[],[f29])).
% 3.53/1.00  
% 3.53/1.00  fof(f82,plain,(
% 3.53/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.53/1.00    inference(definition_unfolding,[],[f44,f56])).
% 3.53/1.00  
% 3.53/1.00  fof(f89,plain,(
% 3.53/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.53/1.00    inference(equality_resolution,[],[f82])).
% 3.53/1.00  
% 3.53/1.00  fof(f12,axiom,(
% 3.53/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f22,plain,(
% 3.53/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f12])).
% 3.53/1.00  
% 3.53/1.00  fof(f39,plain,(
% 3.53/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.53/1.00    inference(nnf_transformation,[],[f22])).
% 3.53/1.00  
% 3.53/1.00  fof(f66,plain,(
% 3.53/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f39])).
% 3.53/1.00  
% 3.53/1.00  fof(f15,axiom,(
% 3.53/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f72,plain,(
% 3.53/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f15])).
% 3.53/1.00  
% 3.53/1.00  fof(f11,axiom,(
% 3.53/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f35,plain,(
% 3.53/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.53/1.00    inference(nnf_transformation,[],[f11])).
% 3.53/1.00  
% 3.53/1.00  fof(f36,plain,(
% 3.53/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.53/1.00    inference(rectify,[],[f35])).
% 3.53/1.00  
% 3.53/1.00  fof(f37,plain,(
% 3.53/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f38,plain,(
% 3.53/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 3.53/1.00  
% 3.53/1.00  fof(f62,plain,(
% 3.53/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.53/1.00    inference(cnf_transformation,[],[f38])).
% 3.53/1.00  
% 3.53/1.00  fof(f91,plain,(
% 3.53/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.53/1.00    inference(equality_resolution,[],[f62])).
% 3.53/1.00  
% 3.53/1.00  fof(f75,plain,(
% 3.53/1.00    k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 3.53/1.00    inference(cnf_transformation,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f85,plain,(
% 3.53/1.00    k1_xboole_0 != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 3.53/1.00    inference(definition_unfolding,[],[f75,f70])).
% 3.53/1.00  
% 3.53/1.00  fof(f8,axiom,(
% 3.53/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f59,plain,(
% 3.53/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f8])).
% 3.53/1.00  
% 3.53/1.00  fof(f83,plain,(
% 3.53/1.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.53/1.00    inference(definition_unfolding,[],[f59,f56])).
% 3.53/1.00  
% 3.53/1.00  fof(f67,plain,(
% 3.53/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f39])).
% 3.53/1.00  
% 3.53/1.00  fof(f63,plain,(
% 3.53/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.53/1.00    inference(cnf_transformation,[],[f38])).
% 3.53/1.00  
% 3.53/1.00  fof(f90,plain,(
% 3.53/1.00    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f63])).
% 3.53/1.00  
% 3.53/1.00  cnf(c_12,plain,
% 3.53/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1743,plain,
% 3.53/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_28,negated_conjecture,
% 3.53/1.00      ( r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 = sK5 ),
% 3.53/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1735,plain,
% 3.53/1.00      ( k1_xboole_0 = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_13,plain,
% 3.53/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1742,plain,
% 3.53/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3987,plain,
% 3.53/1.00      ( k3_xboole_0(sK5,k3_subset_1(sK4,sK5)) = sK5 | sK5 = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1735,c_1742]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,X1)
% 3.53/1.00      | r2_hidden(X0,X2)
% 3.53/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1751,plain,
% 3.53/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.53/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.53/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_15838,plain,
% 3.53/1.00      ( sK5 = k1_xboole_0
% 3.53/1.00      | r2_hidden(X0,k3_subset_1(sK4,sK5)) = iProver_top
% 3.53/1.00      | r2_hidden(X0,k5_xboole_0(sK5,sK5)) = iProver_top
% 3.53/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3987,c_1751]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_14,plain,
% 3.53/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_0,plain,
% 3.53/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2166,plain,
% 3.53/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_14,c_0]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_16,plain,
% 3.53/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2174,plain,
% 3.53/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2166,c_14,c_16]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3008,plain,
% 3.53/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2174,c_0]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3011,plain,
% 3.53/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_3008,c_14,c_16]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3012,plain,
% 3.53/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_3011,c_2174]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_15881,plain,
% 3.53/1.00      ( sK5 = k1_xboole_0
% 3.53/1.00      | r2_hidden(X0,k3_subset_1(sK4,sK5)) = iProver_top
% 3.53/1.00      | r2_hidden(X0,sK5) != iProver_top
% 3.53/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_15838,c_3012]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_25,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.53/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_29,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_485,plain,
% 3.53/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.53/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
% 3.53/1.00      | sK5 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_486,plain,
% 3.53/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,sK5)) = k3_subset_1(X0,sK5)
% 3.53/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_485]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1918,plain,
% 3.53/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k3_subset_1(sK4,sK5) ),
% 3.53/1.00      inference(equality_resolution,[status(thm)],[c_486]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,X1)
% 3.53/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1750,plain,
% 3.53/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.53/1.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7328,plain,
% 3.53/1.00      ( r2_hidden(X0,k3_subset_1(sK4,sK5)) != iProver_top
% 3.53/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1918,c_1750]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7341,plain,
% 3.53/1.00      ( r2_hidden(X0,k5_xboole_0(X1,k1_xboole_0)) != iProver_top
% 3.53/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_14,c_1750]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7389,plain,
% 3.53/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.53/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7341,c_16]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6,plain,
% 3.53/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1749,plain,
% 3.53/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.53/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5237,plain,
% 3.53/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.53/1.00      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_0,c_1749]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7030,plain,
% 3.53/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.53/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_14,c_5237]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8314,plain,
% 3.53/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7389,c_7030]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_16583,plain,
% 3.53/1.00      ( r2_hidden(X0,sK5) != iProver_top | sK5 = k1_xboole_0 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_15881,c_7030,c_7389,c_7328]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_16584,plain,
% 3.53/1.00      ( sK5 = k1_xboole_0 | r2_hidden(X0,sK5) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_16583]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_16593,plain,
% 3.53/1.00      ( sK5 = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1743,c_16584]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_24,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_472,plain,
% 3.53/1.00      ( r2_hidden(X0,X1)
% 3.53/1.00      | v1_xboole_0(X1)
% 3.53/1.00      | k1_zfmisc_1(sK4) != X1
% 3.53/1.00      | sK5 != X0 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_473,plain,
% 3.53/1.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) | v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_472]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_26,plain,
% 3.53/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_479,plain,
% 3.53/1.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
% 3.53/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_473,c_26]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1734,plain,
% 3.53/1.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_20,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1737,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.53/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2824,plain,
% 3.53/1.00      ( r1_tarski(sK5,sK4) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1734,c_1737]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17787,plain,
% 3.53/1.00      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_16593,c_2824]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_27,negated_conjecture,
% 3.53/1.00      ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 != sK5 ),
% 3.53/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1736,plain,
% 3.53/1.00      ( k1_xboole_0 != sK5
% 3.53/1.00      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17799,plain,
% 3.53/1.00      ( k1_xboole_0 != k1_xboole_0
% 3.53/1.00      | r1_tarski(k1_xboole_0,k3_subset_1(sK4,k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_16593,c_1736]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17800,plain,
% 3.53/1.00      ( r1_tarski(k1_xboole_0,k3_subset_1(sK4,k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_17799]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_15,plain,
% 3.53/1.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1741,plain,
% 3.53/1.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2168,plain,
% 3.53/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_0,c_1741]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2235,plain,
% 3.53/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_14,c_2168]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_23,plain,
% 3.53/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_452,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,X1)
% 3.53/1.00      | v1_xboole_0(X1)
% 3.53/1.00      | X2 != X0
% 3.53/1.00      | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
% 3.53/1.00      | k1_zfmisc_1(X3) != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_453,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.53/1.00      | v1_xboole_0(k1_zfmisc_1(X1))
% 3.53/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_452]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_463,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.53/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.53/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_453,c_26]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_19,plain,
% 3.53/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_778,plain,
% 3.53/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.53/1.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_835,plain,
% 3.53/1.00      ( ~ r1_tarski(X0,X1)
% 3.53/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.53/1.00      inference(bin_hyper_res,[status(thm)],[c_463,c_778]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1733,plain,
% 3.53/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.53/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_835]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2346,plain,
% 3.53/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2235,c_1733]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2347,plain,
% 3.53/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2346,c_14,c_16]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17802,plain,
% 3.53/1.00      ( r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_17800,c_2347]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17820,plain,
% 3.53/1.00      ( $false ),
% 3.53/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_17787,c_17802]) ).
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  ------                               Statistics
% 3.53/1.00  
% 3.53/1.00  ------ General
% 3.53/1.00  
% 3.53/1.00  abstr_ref_over_cycles:                  0
% 3.53/1.00  abstr_ref_under_cycles:                 0
% 3.53/1.00  gc_basic_clause_elim:                   0
% 3.53/1.00  forced_gc_time:                         0
% 3.53/1.00  parsing_time:                           0.039
% 3.53/1.00  unif_index_cands_time:                  0.
% 3.53/1.00  unif_index_add_time:                    0.
% 3.53/1.00  orderings_time:                         0.
% 3.53/1.00  out_proof_time:                         0.009
% 3.53/1.00  total_time:                             0.491
% 3.53/1.00  num_of_symbols:                         47
% 3.53/1.00  num_of_terms:                           17783
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing
% 3.53/1.00  
% 3.53/1.00  num_of_splits:                          0
% 3.53/1.00  num_of_split_atoms:                     0
% 3.53/1.00  num_of_reused_defs:                     0
% 3.53/1.00  num_eq_ax_congr_red:                    36
% 3.53/1.00  num_of_sem_filtered_clauses:            1
% 3.53/1.00  num_of_subtypes:                        0
% 3.53/1.00  monotx_restored_types:                  0
% 3.53/1.00  sat_num_of_epr_types:                   0
% 3.53/1.00  sat_num_of_non_cyclic_types:            0
% 3.53/1.00  sat_guarded_non_collapsed_types:        0
% 3.53/1.00  num_pure_diseq_elim:                    0
% 3.53/1.00  simp_replaced_by:                       0
% 3.53/1.00  res_preprocessed:                       125
% 3.53/1.00  prep_upred:                             0
% 3.53/1.00  prep_unflattend:                        55
% 3.53/1.00  smt_new_axioms:                         0
% 3.53/1.00  pred_elim_cands:                        3
% 3.53/1.00  pred_elim:                              2
% 3.53/1.00  pred_elim_cl:                           4
% 3.53/1.00  pred_elim_cycles:                       6
% 3.53/1.00  merged_defs:                            24
% 3.53/1.00  merged_defs_ncl:                        0
% 3.53/1.00  bin_hyper_res:                          25
% 3.53/1.00  prep_cycles:                            4
% 3.53/1.00  pred_elim_time:                         0.009
% 3.53/1.00  splitting_time:                         0.
% 3.53/1.00  sem_filter_time:                        0.
% 3.53/1.00  monotx_time:                            0.
% 3.53/1.00  subtype_inf_time:                       0.
% 3.53/1.00  
% 3.53/1.00  ------ Problem properties
% 3.53/1.00  
% 3.53/1.00  clauses:                                26
% 3.53/1.00  conjectures:                            2
% 3.53/1.00  epr:                                    1
% 3.53/1.00  horn:                                   17
% 3.53/1.00  ground:                                 3
% 3.53/1.00  unary:                                  5
% 3.53/1.00  binary:                                 14
% 3.53/1.00  lits:                                   55
% 3.53/1.00  lits_eq:                                17
% 3.53/1.00  fd_pure:                                0
% 3.53/1.00  fd_pseudo:                              0
% 3.53/1.00  fd_cond:                                1
% 3.53/1.00  fd_pseudo_cond:                         5
% 3.53/1.00  ac_symbols:                             0
% 3.53/1.00  
% 3.53/1.00  ------ Propositional Solver
% 3.53/1.00  
% 3.53/1.00  prop_solver_calls:                      29
% 3.53/1.00  prop_fast_solver_calls:                 1027
% 3.53/1.00  smt_solver_calls:                       0
% 3.53/1.00  smt_fast_solver_calls:                  0
% 3.53/1.00  prop_num_of_clauses:                    6800
% 3.53/1.00  prop_preprocess_simplified:             14008
% 3.53/1.00  prop_fo_subsumed:                       11
% 3.53/1.00  prop_solver_time:                       0.
% 3.53/1.00  smt_solver_time:                        0.
% 3.53/1.00  smt_fast_solver_time:                   0.
% 3.53/1.00  prop_fast_solver_time:                  0.
% 3.53/1.00  prop_unsat_core_time:                   0.
% 3.53/1.00  
% 3.53/1.00  ------ QBF
% 3.53/1.00  
% 3.53/1.00  qbf_q_res:                              0
% 3.53/1.00  qbf_num_tautologies:                    0
% 3.53/1.00  qbf_prep_cycles:                        0
% 3.53/1.00  
% 3.53/1.00  ------ BMC1
% 3.53/1.00  
% 3.53/1.00  bmc1_current_bound:                     -1
% 3.53/1.00  bmc1_last_solved_bound:                 -1
% 3.53/1.00  bmc1_unsat_core_size:                   -1
% 3.53/1.00  bmc1_unsat_core_parents_size:           -1
% 3.53/1.00  bmc1_merge_next_fun:                    0
% 3.53/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation
% 3.53/1.00  
% 3.53/1.00  inst_num_of_clauses:                    1650
% 3.53/1.00  inst_num_in_passive:                    636
% 3.53/1.00  inst_num_in_active:                     586
% 3.53/1.00  inst_num_in_unprocessed:                429
% 3.53/1.00  inst_num_of_loops:                      760
% 3.53/1.00  inst_num_of_learning_restarts:          0
% 3.53/1.00  inst_num_moves_active_passive:          172
% 3.53/1.00  inst_lit_activity:                      0
% 3.53/1.00  inst_lit_activity_moves:                0
% 3.53/1.00  inst_num_tautologies:                   0
% 3.53/1.00  inst_num_prop_implied:                  0
% 3.53/1.00  inst_num_existing_simplified:           0
% 3.53/1.00  inst_num_eq_res_simplified:             0
% 3.53/1.00  inst_num_child_elim:                    0
% 3.53/1.00  inst_num_of_dismatching_blockings:      1065
% 3.53/1.00  inst_num_of_non_proper_insts:           1642
% 3.53/1.00  inst_num_of_duplicates:                 0
% 3.53/1.00  inst_inst_num_from_inst_to_res:         0
% 3.53/1.00  inst_dismatching_checking_time:         0.
% 3.53/1.00  
% 3.53/1.00  ------ Resolution
% 3.53/1.00  
% 3.53/1.00  res_num_of_clauses:                     0
% 3.53/1.00  res_num_in_passive:                     0
% 3.53/1.00  res_num_in_active:                      0
% 3.53/1.00  res_num_of_loops:                       129
% 3.53/1.00  res_forward_subset_subsumed:            118
% 3.53/1.00  res_backward_subset_subsumed:           2
% 3.53/1.00  res_forward_subsumed:                   2
% 3.53/1.00  res_backward_subsumed:                  0
% 3.53/1.00  res_forward_subsumption_resolution:     2
% 3.53/1.00  res_backward_subsumption_resolution:    0
% 3.53/1.00  res_clause_to_clause_subsumption:       1490
% 3.53/1.00  res_orphan_elimination:                 0
% 3.53/1.00  res_tautology_del:                      128
% 3.53/1.00  res_num_eq_res_simplified:              0
% 3.53/1.00  res_num_sel_changes:                    0
% 3.53/1.00  res_moves_from_active_to_pass:          0
% 3.53/1.00  
% 3.53/1.00  ------ Superposition
% 3.53/1.00  
% 3.53/1.00  sup_time_total:                         0.
% 3.53/1.00  sup_time_generating:                    0.
% 3.53/1.00  sup_time_sim_full:                      0.
% 3.53/1.00  sup_time_sim_immed:                     0.
% 3.53/1.00  
% 3.53/1.00  sup_num_of_clauses:                     249
% 3.53/1.00  sup_num_in_active:                      37
% 3.53/1.00  sup_num_in_passive:                     212
% 3.53/1.00  sup_num_of_loops:                       150
% 3.53/1.00  sup_fw_superposition:                   364
% 3.53/1.00  sup_bw_superposition:                   368
% 3.53/1.00  sup_immediate_simplified:               260
% 3.53/1.00  sup_given_eliminated:                   1
% 3.53/1.00  comparisons_done:                       0
% 3.53/1.00  comparisons_avoided:                    93
% 3.53/1.00  
% 3.53/1.00  ------ Simplifications
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  sim_fw_subset_subsumed:                 17
% 3.53/1.00  sim_bw_subset_subsumed:                 82
% 3.53/1.00  sim_fw_subsumed:                        57
% 3.53/1.00  sim_bw_subsumed:                        18
% 3.53/1.00  sim_fw_subsumption_res:                 3
% 3.53/1.00  sim_bw_subsumption_res:                 0
% 3.53/1.00  sim_tautology_del:                      25
% 3.53/1.00  sim_eq_tautology_del:                   48
% 3.53/1.00  sim_eq_res_simp:                        5
% 3.53/1.00  sim_fw_demodulated:                     149
% 3.53/1.00  sim_bw_demodulated:                     107
% 3.53/1.00  sim_light_normalised:                   47
% 3.53/1.00  sim_joinable_taut:                      0
% 3.53/1.00  sim_joinable_simp:                      0
% 3.53/1.00  sim_ac_normalised:                      0
% 3.53/1.00  sim_smt_subsumption:                    0
% 3.53/1.00  
%------------------------------------------------------------------------------
