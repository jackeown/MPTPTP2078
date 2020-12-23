%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:52 EST 2020

% Result     : Theorem 15.74s
% Output     : CNFRefutation 15.74s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 319 expanded)
%              Number of clauses        :   52 ( 102 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   19
%              Number of atoms          :  406 (1294 expanded)
%              Number of equality atoms :  133 ( 361 expanded)
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

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f31])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f3])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f41,plain,
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

fof(f42,plain,
    ( ( k1_subset_1(sK4) != sK5
      | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
    & ( k1_subset_1(sK4) = sK5
      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f41])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

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
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,
    ( k1_subset_1(sK4) = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f86,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(definition_unfolding,[],[f74,f70])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f75,plain,
    ( k1_subset_1(sK4) != sK5
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,
    ( k1_xboole_0 != sK5
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(definition_unfolding,[],[f75,f70])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1006,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1007,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2413,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1006,c_1007])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_990,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_995,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1512,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_995])).

cnf(c_1373,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(resolution,[status(thm)],[c_25,c_30])).

cnf(c_27,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1378,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1373,c_27])).

cnf(c_1379,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1378])).

cnf(c_1773,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1512,c_1379])).

cnf(c_21,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_999,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1778,plain,
    ( r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_999])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1005,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1782,plain,
    ( k4_xboole_0(sK5,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1778,c_1005])).

cnf(c_2417,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1782,c_1007])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1003,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2402,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) = sK5 ),
    inference(superposition,[status(thm)],[c_1778,c_1003])).

cnf(c_2404,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_2402,c_1782])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1008,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7131,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2404,c_1008])).

cnf(c_8377,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2417,c_7131])).

cnf(c_15402,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2413,c_8377])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1004,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20809,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15402,c_1004])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_994,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2713,plain,
    ( k3_subset_1(sK4,sK5) = k4_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_990,c_994])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_991,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2929,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k4_xboole_0(sK4,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2713,c_991])).

cnf(c_3040,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK5))) = sK5
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2929,c_1003])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1014,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4262,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k4_xboole_0(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3040,c_1014])).

cnf(c_6359,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4262,c_1008])).

cnf(c_6363,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1006,c_6359])).

cnf(c_28,negated_conjecture,
    ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_992,plain,
    ( k1_xboole_0 != sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2930,plain,
    ( sK5 != k1_xboole_0
    | r1_tarski(sK5,k4_xboole_0(sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2713,c_992])).

cnf(c_18787,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k4_xboole_0(sK4,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6363,c_2930])).

cnf(c_18803,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(sK4,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18787])).

cnf(c_63801,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_20809,c_18803])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:13:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 15.74/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.74/2.51  
% 15.74/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.74/2.51  
% 15.74/2.51  ------  iProver source info
% 15.74/2.51  
% 15.74/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.74/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.74/2.51  git: non_committed_changes: false
% 15.74/2.51  git: last_make_outside_of_git: false
% 15.74/2.51  
% 15.74/2.51  ------ 
% 15.74/2.51  ------ Parsing...
% 15.74/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.74/2.51  
% 15.74/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.74/2.51  
% 15.74/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.74/2.51  
% 15.74/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.74/2.51  ------ Proving...
% 15.74/2.51  ------ Problem Properties 
% 15.74/2.51  
% 15.74/2.51  
% 15.74/2.51  clauses                                 31
% 15.74/2.51  conjectures                             3
% 15.74/2.51  EPR                                     4
% 15.74/2.51  Horn                                    20
% 15.74/2.51  unary                                   4
% 15.74/2.51  binary                                  13
% 15.74/2.51  lits                                    74
% 15.74/2.51  lits eq                                 17
% 15.74/2.51  fd_pure                                 0
% 15.74/2.51  fd_pseudo                               0
% 15.74/2.51  fd_cond                                 1
% 15.74/2.51  fd_pseudo_cond                          8
% 15.74/2.51  AC symbols                              0
% 15.74/2.51  
% 15.74/2.51  ------ Input Options Time Limit: Unbounded
% 15.74/2.51  
% 15.74/2.51  
% 15.74/2.51  ------ 
% 15.74/2.51  Current options:
% 15.74/2.51  ------ 
% 15.74/2.51  
% 15.74/2.51  
% 15.74/2.51  
% 15.74/2.51  
% 15.74/2.51  ------ Proving...
% 15.74/2.51  
% 15.74/2.51  
% 15.74/2.51  % SZS status Theorem for theBenchmark.p
% 15.74/2.51  
% 15.74/2.51   Resolution empty clause
% 15.74/2.51  
% 15.74/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.74/2.51  
% 15.74/2.51  fof(f4,axiom,(
% 15.74/2.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f16,plain,(
% 15.74/2.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 15.74/2.51    inference(ennf_transformation,[],[f4])).
% 15.74/2.51  
% 15.74/2.51  fof(f31,plain,(
% 15.74/2.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 15.74/2.51    introduced(choice_axiom,[])).
% 15.74/2.51  
% 15.74/2.51  fof(f32,plain,(
% 15.74/2.51    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 15.74/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f31])).
% 15.74/2.51  
% 15.74/2.51  fof(f56,plain,(
% 15.74/2.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 15.74/2.51    inference(cnf_transformation,[],[f32])).
% 15.74/2.51  
% 15.74/2.51  fof(f3,axiom,(
% 15.74/2.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f26,plain,(
% 15.74/2.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.74/2.51    inference(nnf_transformation,[],[f3])).
% 15.74/2.51  
% 15.74/2.51  fof(f27,plain,(
% 15.74/2.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.74/2.51    inference(flattening,[],[f26])).
% 15.74/2.51  
% 15.74/2.51  fof(f28,plain,(
% 15.74/2.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.74/2.51    inference(rectify,[],[f27])).
% 15.74/2.51  
% 15.74/2.51  fof(f29,plain,(
% 15.74/2.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 15.74/2.51    introduced(choice_axiom,[])).
% 15.74/2.51  
% 15.74/2.51  fof(f30,plain,(
% 15.74/2.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.74/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 15.74/2.51  
% 15.74/2.51  fof(f50,plain,(
% 15.74/2.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 15.74/2.51    inference(cnf_transformation,[],[f30])).
% 15.74/2.51  
% 15.74/2.51  fof(f92,plain,(
% 15.74/2.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 15.74/2.51    inference(equality_resolution,[],[f50])).
% 15.74/2.51  
% 15.74/2.51  fof(f14,conjecture,(
% 15.74/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f15,negated_conjecture,(
% 15.74/2.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 15.74/2.51    inference(negated_conjecture,[],[f14])).
% 15.74/2.51  
% 15.74/2.51  fof(f20,plain,(
% 15.74/2.51    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.74/2.51    inference(ennf_transformation,[],[f15])).
% 15.74/2.51  
% 15.74/2.51  fof(f39,plain,(
% 15.74/2.51    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.74/2.51    inference(nnf_transformation,[],[f20])).
% 15.74/2.51  
% 15.74/2.51  fof(f40,plain,(
% 15.74/2.51    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.74/2.51    inference(flattening,[],[f39])).
% 15.74/2.51  
% 15.74/2.51  fof(f41,plain,(
% 15.74/2.51    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))) & (k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 15.74/2.51    introduced(choice_axiom,[])).
% 15.74/2.51  
% 15.74/2.51  fof(f42,plain,(
% 15.74/2.51    (k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))) & (k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 15.74/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f41])).
% 15.74/2.51  
% 15.74/2.51  fof(f73,plain,(
% 15.74/2.51    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 15.74/2.51    inference(cnf_transformation,[],[f42])).
% 15.74/2.51  
% 15.74/2.51  fof(f10,axiom,(
% 15.74/2.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f18,plain,(
% 15.74/2.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 15.74/2.51    inference(ennf_transformation,[],[f10])).
% 15.74/2.51  
% 15.74/2.51  fof(f38,plain,(
% 15.74/2.51    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 15.74/2.51    inference(nnf_transformation,[],[f18])).
% 15.74/2.51  
% 15.74/2.51  fof(f66,plain,(
% 15.74/2.51    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 15.74/2.51    inference(cnf_transformation,[],[f38])).
% 15.74/2.51  
% 15.74/2.51  fof(f13,axiom,(
% 15.74/2.51    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f72,plain,(
% 15.74/2.51    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 15.74/2.51    inference(cnf_transformation,[],[f13])).
% 15.74/2.51  
% 15.74/2.51  fof(f9,axiom,(
% 15.74/2.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f34,plain,(
% 15.74/2.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.74/2.51    inference(nnf_transformation,[],[f9])).
% 15.74/2.51  
% 15.74/2.51  fof(f35,plain,(
% 15.74/2.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.74/2.51    inference(rectify,[],[f34])).
% 15.74/2.51  
% 15.74/2.51  fof(f36,plain,(
% 15.74/2.51    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 15.74/2.51    introduced(choice_axiom,[])).
% 15.74/2.51  
% 15.74/2.51  fof(f37,plain,(
% 15.74/2.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.74/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 15.74/2.51  
% 15.74/2.51  fof(f62,plain,(
% 15.74/2.51    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 15.74/2.51    inference(cnf_transformation,[],[f37])).
% 15.74/2.51  
% 15.74/2.51  fof(f94,plain,(
% 15.74/2.51    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 15.74/2.51    inference(equality_resolution,[],[f62])).
% 15.74/2.51  
% 15.74/2.51  fof(f5,axiom,(
% 15.74/2.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f33,plain,(
% 15.74/2.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.74/2.51    inference(nnf_transformation,[],[f5])).
% 15.74/2.51  
% 15.74/2.51  fof(f58,plain,(
% 15.74/2.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.74/2.51    inference(cnf_transformation,[],[f33])).
% 15.74/2.51  
% 15.74/2.51  fof(f7,axiom,(
% 15.74/2.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f17,plain,(
% 15.74/2.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.74/2.51    inference(ennf_transformation,[],[f7])).
% 15.74/2.51  
% 15.74/2.51  fof(f60,plain,(
% 15.74/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.74/2.51    inference(cnf_transformation,[],[f17])).
% 15.74/2.51  
% 15.74/2.51  fof(f8,axiom,(
% 15.74/2.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f61,plain,(
% 15.74/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.74/2.51    inference(cnf_transformation,[],[f8])).
% 15.74/2.51  
% 15.74/2.51  fof(f84,plain,(
% 15.74/2.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 15.74/2.51    inference(definition_unfolding,[],[f60,f61])).
% 15.74/2.51  
% 15.74/2.51  fof(f51,plain,(
% 15.74/2.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 15.74/2.51    inference(cnf_transformation,[],[f30])).
% 15.74/2.51  
% 15.74/2.51  fof(f91,plain,(
% 15.74/2.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 15.74/2.51    inference(equality_resolution,[],[f51])).
% 15.74/2.51  
% 15.74/2.51  fof(f57,plain,(
% 15.74/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.74/2.51    inference(cnf_transformation,[],[f33])).
% 15.74/2.51  
% 15.74/2.51  fof(f12,axiom,(
% 15.74/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f19,plain,(
% 15.74/2.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.74/2.51    inference(ennf_transformation,[],[f12])).
% 15.74/2.51  
% 15.74/2.51  fof(f71,plain,(
% 15.74/2.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.74/2.51    inference(cnf_transformation,[],[f19])).
% 15.74/2.51  
% 15.74/2.51  fof(f74,plain,(
% 15.74/2.51    k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 15.74/2.51    inference(cnf_transformation,[],[f42])).
% 15.74/2.51  
% 15.74/2.51  fof(f11,axiom,(
% 15.74/2.51    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f70,plain,(
% 15.74/2.51    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 15.74/2.51    inference(cnf_transformation,[],[f11])).
% 15.74/2.51  
% 15.74/2.51  fof(f86,plain,(
% 15.74/2.51    k1_xboole_0 = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 15.74/2.51    inference(definition_unfolding,[],[f74,f70])).
% 15.74/2.51  
% 15.74/2.51  fof(f2,axiom,(
% 15.74/2.51    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.74/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.74/2.51  
% 15.74/2.51  fof(f21,plain,(
% 15.74/2.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.74/2.51    inference(nnf_transformation,[],[f2])).
% 15.74/2.51  
% 15.74/2.51  fof(f22,plain,(
% 15.74/2.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.74/2.51    inference(flattening,[],[f21])).
% 15.74/2.51  
% 15.74/2.51  fof(f23,plain,(
% 15.74/2.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.74/2.51    inference(rectify,[],[f22])).
% 15.74/2.51  
% 15.74/2.51  fof(f24,plain,(
% 15.74/2.51    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.74/2.51    introduced(choice_axiom,[])).
% 15.74/2.51  
% 15.74/2.51  fof(f25,plain,(
% 15.74/2.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.74/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 15.74/2.51  
% 15.74/2.51  fof(f45,plain,(
% 15.74/2.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.74/2.51    inference(cnf_transformation,[],[f25])).
% 15.74/2.51  
% 15.74/2.51  fof(f82,plain,(
% 15.74/2.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 15.74/2.51    inference(definition_unfolding,[],[f45,f61])).
% 15.74/2.51  
% 15.74/2.51  fof(f88,plain,(
% 15.74/2.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.74/2.51    inference(equality_resolution,[],[f82])).
% 15.74/2.51  
% 15.74/2.51  fof(f75,plain,(
% 15.74/2.51    k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 15.74/2.51    inference(cnf_transformation,[],[f42])).
% 15.74/2.51  
% 15.74/2.51  fof(f85,plain,(
% 15.74/2.51    k1_xboole_0 != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 15.74/2.51    inference(definition_unfolding,[],[f75,f70])).
% 15.74/2.51  
% 15.74/2.51  cnf(c_14,plain,
% 15.74/2.51      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 15.74/2.51      inference(cnf_transformation,[],[f56]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1006,plain,
% 15.74/2.51      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_13,plain,
% 15.74/2.51      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 15.74/2.51      inference(cnf_transformation,[],[f92]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1007,plain,
% 15.74/2.51      ( r2_hidden(X0,X1) = iProver_top
% 15.74/2.51      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_2413,plain,
% 15.74/2.51      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 15.74/2.51      | r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_1006,c_1007]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_30,negated_conjecture,
% 15.74/2.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 15.74/2.51      inference(cnf_transformation,[],[f73]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_990,plain,
% 15.74/2.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_25,plain,
% 15.74/2.51      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.74/2.51      inference(cnf_transformation,[],[f66]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_995,plain,
% 15.74/2.51      ( m1_subset_1(X0,X1) != iProver_top
% 15.74/2.51      | r2_hidden(X0,X1) = iProver_top
% 15.74/2.51      | v1_xboole_0(X1) = iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1512,plain,
% 15.74/2.51      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
% 15.74/2.51      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_990,c_995]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1373,plain,
% 15.74/2.51      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) | v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 15.74/2.51      inference(resolution,[status(thm)],[c_25,c_30]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_27,plain,
% 15.74/2.51      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 15.74/2.51      inference(cnf_transformation,[],[f72]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1378,plain,
% 15.74/2.51      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
% 15.74/2.51      inference(forward_subsumption_resolution,[status(thm)],[c_1373,c_27]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1379,plain,
% 15.74/2.51      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_1378]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1773,plain,
% 15.74/2.51      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 15.74/2.51      inference(global_propositional_subsumption,[status(thm)],[c_1512,c_1379]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_21,plain,
% 15.74/2.51      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 15.74/2.51      inference(cnf_transformation,[],[f94]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_999,plain,
% 15.74/2.51      ( r1_tarski(X0,X1) = iProver_top
% 15.74/2.51      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1778,plain,
% 15.74/2.51      ( r1_tarski(sK5,sK4) = iProver_top ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_1773,c_999]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_15,plain,
% 15.74/2.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.74/2.51      inference(cnf_transformation,[],[f58]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1005,plain,
% 15.74/2.51      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1782,plain,
% 15.74/2.51      ( k4_xboole_0(sK5,sK4) = k1_xboole_0 ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_1778,c_1005]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_2417,plain,
% 15.74/2.51      ( r2_hidden(X0,sK5) = iProver_top
% 15.74/2.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_1782,c_1007]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_17,plain,
% 15.74/2.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 15.74/2.51      inference(cnf_transformation,[],[f84]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1003,plain,
% 15.74/2.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 15.74/2.51      | r1_tarski(X0,X1) != iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_2402,plain,
% 15.74/2.51      ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) = sK5 ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_1778,c_1003]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_2404,plain,
% 15.74/2.51      ( k4_xboole_0(sK5,k1_xboole_0) = sK5 ),
% 15.74/2.51      inference(light_normalisation,[status(thm)],[c_2402,c_1782]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_12,plain,
% 15.74/2.51      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 15.74/2.51      inference(cnf_transformation,[],[f91]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1008,plain,
% 15.74/2.51      ( r2_hidden(X0,X1) != iProver_top
% 15.74/2.51      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_7131,plain,
% 15.74/2.51      ( r2_hidden(X0,sK5) != iProver_top
% 15.74/2.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_2404,c_1008]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_8377,plain,
% 15.74/2.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.74/2.51      inference(global_propositional_subsumption,[status(thm)],[c_2417,c_7131]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_15402,plain,
% 15.74/2.51      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_2413,c_8377]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_16,plain,
% 15.74/2.51      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.74/2.51      inference(cnf_transformation,[],[f57]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1004,plain,
% 15.74/2.51      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_20809,plain,
% 15.74/2.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_15402,c_1004]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_26,plain,
% 15.74/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.74/2.51      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 15.74/2.51      inference(cnf_transformation,[],[f71]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_994,plain,
% 15.74/2.51      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 15.74/2.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_2713,plain,
% 15.74/2.51      ( k3_subset_1(sK4,sK5) = k4_xboole_0(sK4,sK5) ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_990,c_994]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_29,negated_conjecture,
% 15.74/2.51      ( r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 = sK5 ),
% 15.74/2.51      inference(cnf_transformation,[],[f86]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_991,plain,
% 15.74/2.51      ( k1_xboole_0 = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_2929,plain,
% 15.74/2.51      ( sK5 = k1_xboole_0 | r1_tarski(sK5,k4_xboole_0(sK4,sK5)) = iProver_top ),
% 15.74/2.51      inference(demodulation,[status(thm)],[c_2713,c_991]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_3040,plain,
% 15.74/2.51      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK5))) = sK5
% 15.74/2.51      | sK5 = k1_xboole_0 ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_2929,c_1003]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_6,plain,
% 15.74/2.51      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 15.74/2.51      inference(cnf_transformation,[],[f88]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_1014,plain,
% 15.74/2.51      ( r2_hidden(X0,X1) = iProver_top
% 15.74/2.51      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_4262,plain,
% 15.74/2.51      ( sK5 = k1_xboole_0
% 15.74/2.51      | r2_hidden(X0,k4_xboole_0(sK4,sK5)) = iProver_top
% 15.74/2.51      | r2_hidden(X0,sK5) != iProver_top ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_3040,c_1014]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_6359,plain,
% 15.74/2.51      ( sK5 = k1_xboole_0 | r2_hidden(X0,sK5) != iProver_top ),
% 15.74/2.51      inference(forward_subsumption_resolution,[status(thm)],[c_4262,c_1008]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_6363,plain,
% 15.74/2.51      ( sK5 = k1_xboole_0 ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_1006,c_6359]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_28,negated_conjecture,
% 15.74/2.51      ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 != sK5 ),
% 15.74/2.51      inference(cnf_transformation,[],[f85]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_992,plain,
% 15.74/2.51      ( k1_xboole_0 != sK5
% 15.74/2.51      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) != iProver_top ),
% 15.74/2.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_2930,plain,
% 15.74/2.51      ( sK5 != k1_xboole_0
% 15.74/2.51      | r1_tarski(sK5,k4_xboole_0(sK4,sK5)) != iProver_top ),
% 15.74/2.51      inference(demodulation,[status(thm)],[c_2713,c_992]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_18787,plain,
% 15.74/2.51      ( k1_xboole_0 != k1_xboole_0
% 15.74/2.51      | r1_tarski(k1_xboole_0,k4_xboole_0(sK4,k1_xboole_0)) != iProver_top ),
% 15.74/2.51      inference(demodulation,[status(thm)],[c_6363,c_2930]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_18803,plain,
% 15.74/2.51      ( r1_tarski(k1_xboole_0,k4_xboole_0(sK4,k1_xboole_0)) != iProver_top ),
% 15.74/2.51      inference(equality_resolution_simp,[status(thm)],[c_18787]) ).
% 15.74/2.51  
% 15.74/2.51  cnf(c_63801,plain,
% 15.74/2.51      ( $false ),
% 15.74/2.51      inference(superposition,[status(thm)],[c_20809,c_18803]) ).
% 15.74/2.51  
% 15.74/2.51  
% 15.74/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.74/2.51  
% 15.74/2.51  ------                               Statistics
% 15.74/2.51  
% 15.74/2.51  ------ Selected
% 15.74/2.51  
% 15.74/2.51  total_time:                             1.765
% 15.74/2.51  
%------------------------------------------------------------------------------
