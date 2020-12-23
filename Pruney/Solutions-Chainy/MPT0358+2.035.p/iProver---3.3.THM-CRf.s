%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:54 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 860 expanded)
%              Number of clauses        :   73 ( 269 expanded)
%              Number of leaves         :   22 ( 221 expanded)
%              Depth                    :   25
%              Number of atoms          :  414 (2449 expanded)
%              Number of equality atoms :  166 ( 974 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f29])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f52])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK3) != sK4
        | ~ r1_tarski(sK4,k3_subset_1(sK3,sK4)) )
      & ( k1_subset_1(sK3) = sK4
        | r1_tarski(sK4,k3_subset_1(sK3,sK4)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( k1_subset_1(sK3) != sK4
      | ~ r1_tarski(sK4,k3_subset_1(sK3,sK4)) )
    & ( k1_subset_1(sK3) = sK4
      | r1_tarski(sK4,k3_subset_1(sK3,sK4)) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f40])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f55,f52,f52])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f72,plain,
    ( k1_subset_1(sK3) = sK4
    | r1_tarski(sK4,k3_subset_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f85,plain,
    ( k1_xboole_0 = sK4
    | r1_tarski(sK4,k3_subset_1(sK3,sK4)) ),
    inference(definition_unfolding,[],[f72,f65])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,
    ( k1_subset_1(sK3) != sK4
    | ~ r1_tarski(sK4,k3_subset_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,
    ( k1_xboole_0 != sK4
    | ~ r1_tarski(sK4,k3_subset_1(sK3,sK4)) ),
    inference(definition_unfolding,[],[f73,f65])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1089,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_403,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_404,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_1242,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
    inference(equality_resolution,[status(thm)],[c_404])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1092,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7831,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1092])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1091,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4262,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1091])).

cnf(c_12,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4275,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1091])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4302,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4275,c_13])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1090,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2909,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1090])).

cnf(c_3043,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_2909])).

cnf(c_4518,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4302,c_3043])).

cnf(c_1370,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_1375,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1370,c_12,c_13])).

cnf(c_1444,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1375,c_0])).

cnf(c_1446,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1444,c_12,c_13])).

cnf(c_1447,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1446,c_1375])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(sK4,k3_subset_1(sK3,sK4))
    | k1_xboole_0 = sK4 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1080,plain,
    ( k1_xboole_0 = sK4
    | r1_tarski(sK4,k3_subset_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1086,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1973,plain,
    ( k3_xboole_0(sK4,k3_subset_1(sK3,sK4)) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1080,c_1086])).

cnf(c_2100,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,sK4))) = k3_xboole_0(sK4,k3_subset_1(sK3,sK4))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1973,c_0])).

cnf(c_2103,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK3,sK4)))) = k3_xboole_0(sK4,k5_xboole_0(sK4,sK4))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2100,c_0])).

cnf(c_6926,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK3,sK4)))) = k3_xboole_0(sK4,k1_xboole_0)
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1447,c_2103])).

cnf(c_1371,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_6933,plain,
    ( k3_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK3,sK4)))) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6926,c_12,c_1371])).

cnf(c_26,negated_conjecture,
    ( ~ r1_tarski(sK4,k3_subset_1(sK3,sK4))
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_68,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_72,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_619,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1283,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,k3_subset_1(sK3,sK4))
    | k3_subset_1(sK3,sK4) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_1412,plain,
    ( ~ r1_tarski(X0,k3_subset_1(sK3,sK4))
    | r1_tarski(sK4,k3_subset_1(sK3,sK4))
    | k3_subset_1(sK3,sK4) != k3_subset_1(sK3,sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1283])).

cnf(c_1415,plain,
    ( r1_tarski(sK4,k3_subset_1(sK3,sK4))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK3,sK4))
    | k3_subset_1(sK3,sK4) != k3_subset_1(sK3,sK4)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_614,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1413,plain,
    ( k3_subset_1(sK3,sK4) = k3_subset_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_615,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1459,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_1460,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1501,plain,
    ( r1_tarski(X0,k3_subset_1(sK3,sK4))
    | ~ r2_hidden(X0,k1_zfmisc_1(k3_subset_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1503,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK3,sK4))
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_subset_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_364,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(X2) != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_365,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_24,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_369,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_24])).

cnf(c_7072,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_subset_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_7122,plain,
    ( k3_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK3,sK4)))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6933,c_26,c_68,c_72,c_1415,c_1413,c_1460,c_1503,c_7072])).

cnf(c_7131,plain,
    ( k3_xboole_0(sK4,k3_subset_1(sK3,sK4)) = k5_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7122,c_0])).

cnf(c_7149,plain,
    ( k3_xboole_0(sK4,k3_subset_1(sK3,sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_7131,c_13])).

cnf(c_7847,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,k5_xboole_0(sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7149,c_1092])).

cnf(c_7868,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7847,c_1447])).

cnf(c_8019,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7831,c_3043,c_4262,c_4302,c_7868])).

cnf(c_8020,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8019])).

cnf(c_8028,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8020,c_4262])).

cnf(c_8280,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8028,c_3043,c_4262,c_4302,c_7868])).

cnf(c_8287,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1089,c_8280])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8287,c_7072,c_1503,c_1460,c_1413,c_1415,c_72,c_68,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.20/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.00  
% 3.20/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/1.00  
% 3.20/1.00  ------  iProver source info
% 3.20/1.00  
% 3.20/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.20/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/1.00  git: non_committed_changes: false
% 3.20/1.00  git: last_make_outside_of_git: false
% 3.20/1.00  
% 3.20/1.00  ------ 
% 3.20/1.00  
% 3.20/1.00  ------ Input Options
% 3.20/1.00  
% 3.20/1.00  --out_options                           all
% 3.20/1.00  --tptp_safe_out                         true
% 3.20/1.00  --problem_path                          ""
% 3.20/1.00  --include_path                          ""
% 3.20/1.00  --clausifier                            res/vclausify_rel
% 3.20/1.00  --clausifier_options                    --mode clausify
% 3.20/1.00  --stdin                                 false
% 3.20/1.00  --stats_out                             all
% 3.20/1.00  
% 3.20/1.00  ------ General Options
% 3.20/1.00  
% 3.20/1.00  --fof                                   false
% 3.20/1.00  --time_out_real                         305.
% 3.20/1.00  --time_out_virtual                      -1.
% 3.20/1.00  --symbol_type_check                     false
% 3.20/1.00  --clausify_out                          false
% 3.20/1.00  --sig_cnt_out                           false
% 3.20/1.00  --trig_cnt_out                          false
% 3.20/1.00  --trig_cnt_out_tolerance                1.
% 3.20/1.00  --trig_cnt_out_sk_spl                   false
% 3.20/1.00  --abstr_cl_out                          false
% 3.20/1.00  
% 3.20/1.00  ------ Global Options
% 3.20/1.00  
% 3.20/1.00  --schedule                              default
% 3.20/1.00  --add_important_lit                     false
% 3.20/1.00  --prop_solver_per_cl                    1000
% 3.20/1.00  --min_unsat_core                        false
% 3.20/1.00  --soft_assumptions                      false
% 3.20/1.00  --soft_lemma_size                       3
% 3.20/1.00  --prop_impl_unit_size                   0
% 3.20/1.00  --prop_impl_unit                        []
% 3.20/1.00  --share_sel_clauses                     true
% 3.20/1.00  --reset_solvers                         false
% 3.20/1.00  --bc_imp_inh                            [conj_cone]
% 3.20/1.00  --conj_cone_tolerance                   3.
% 3.20/1.00  --extra_neg_conj                        none
% 3.20/1.00  --large_theory_mode                     true
% 3.20/1.00  --prolific_symb_bound                   200
% 3.20/1.00  --lt_threshold                          2000
% 3.20/1.00  --clause_weak_htbl                      true
% 3.20/1.00  --gc_record_bc_elim                     false
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing Options
% 3.20/1.00  
% 3.20/1.00  --preprocessing_flag                    true
% 3.20/1.00  --time_out_prep_mult                    0.1
% 3.20/1.00  --splitting_mode                        input
% 3.20/1.00  --splitting_grd                         true
% 3.20/1.00  --splitting_cvd                         false
% 3.20/1.00  --splitting_cvd_svl                     false
% 3.20/1.00  --splitting_nvd                         32
% 3.20/1.00  --sub_typing                            true
% 3.20/1.00  --prep_gs_sim                           true
% 3.20/1.00  --prep_unflatten                        true
% 3.20/1.00  --prep_res_sim                          true
% 3.20/1.00  --prep_upred                            true
% 3.20/1.00  --prep_sem_filter                       exhaustive
% 3.20/1.00  --prep_sem_filter_out                   false
% 3.20/1.00  --pred_elim                             true
% 3.20/1.00  --res_sim_input                         true
% 3.20/1.00  --eq_ax_congr_red                       true
% 3.20/1.00  --pure_diseq_elim                       true
% 3.20/1.00  --brand_transform                       false
% 3.20/1.00  --non_eq_to_eq                          false
% 3.20/1.00  --prep_def_merge                        true
% 3.20/1.00  --prep_def_merge_prop_impl              false
% 3.20/1.00  --prep_def_merge_mbd                    true
% 3.20/1.00  --prep_def_merge_tr_red                 false
% 3.20/1.00  --prep_def_merge_tr_cl                  false
% 3.20/1.00  --smt_preprocessing                     true
% 3.20/1.00  --smt_ac_axioms                         fast
% 3.20/1.00  --preprocessed_out                      false
% 3.20/1.00  --preprocessed_stats                    false
% 3.20/1.00  
% 3.20/1.00  ------ Abstraction refinement Options
% 3.20/1.00  
% 3.20/1.00  --abstr_ref                             []
% 3.20/1.00  --abstr_ref_prep                        false
% 3.20/1.00  --abstr_ref_until_sat                   false
% 3.20/1.00  --abstr_ref_sig_restrict                funpre
% 3.20/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.00  --abstr_ref_under                       []
% 3.20/1.00  
% 3.20/1.00  ------ SAT Options
% 3.20/1.00  
% 3.20/1.00  --sat_mode                              false
% 3.20/1.00  --sat_fm_restart_options                ""
% 3.20/1.00  --sat_gr_def                            false
% 3.20/1.00  --sat_epr_types                         true
% 3.20/1.00  --sat_non_cyclic_types                  false
% 3.20/1.00  --sat_finite_models                     false
% 3.20/1.00  --sat_fm_lemmas                         false
% 3.20/1.00  --sat_fm_prep                           false
% 3.20/1.00  --sat_fm_uc_incr                        true
% 3.20/1.00  --sat_out_model                         small
% 3.20/1.00  --sat_out_clauses                       false
% 3.20/1.00  
% 3.20/1.00  ------ QBF Options
% 3.20/1.00  
% 3.20/1.00  --qbf_mode                              false
% 3.20/1.00  --qbf_elim_univ                         false
% 3.20/1.00  --qbf_dom_inst                          none
% 3.20/1.00  --qbf_dom_pre_inst                      false
% 3.20/1.00  --qbf_sk_in                             false
% 3.20/1.00  --qbf_pred_elim                         true
% 3.20/1.00  --qbf_split                             512
% 3.20/1.00  
% 3.20/1.00  ------ BMC1 Options
% 3.20/1.00  
% 3.20/1.00  --bmc1_incremental                      false
% 3.20/1.00  --bmc1_axioms                           reachable_all
% 3.20/1.00  --bmc1_min_bound                        0
% 3.20/1.00  --bmc1_max_bound                        -1
% 3.20/1.00  --bmc1_max_bound_default                -1
% 3.20/1.00  --bmc1_symbol_reachability              true
% 3.20/1.00  --bmc1_property_lemmas                  false
% 3.20/1.00  --bmc1_k_induction                      false
% 3.20/1.00  --bmc1_non_equiv_states                 false
% 3.20/1.00  --bmc1_deadlock                         false
% 3.20/1.00  --bmc1_ucm                              false
% 3.20/1.00  --bmc1_add_unsat_core                   none
% 3.20/1.00  --bmc1_unsat_core_children              false
% 3.20/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.00  --bmc1_out_stat                         full
% 3.20/1.00  --bmc1_ground_init                      false
% 3.20/1.00  --bmc1_pre_inst_next_state              false
% 3.20/1.00  --bmc1_pre_inst_state                   false
% 3.20/1.00  --bmc1_pre_inst_reach_state             false
% 3.20/1.00  --bmc1_out_unsat_core                   false
% 3.20/1.00  --bmc1_aig_witness_out                  false
% 3.20/1.00  --bmc1_verbose                          false
% 3.20/1.00  --bmc1_dump_clauses_tptp                false
% 3.20/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.00  --bmc1_dump_file                        -
% 3.20/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.00  --bmc1_ucm_extend_mode                  1
% 3.20/1.00  --bmc1_ucm_init_mode                    2
% 3.20/1.00  --bmc1_ucm_cone_mode                    none
% 3.20/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.00  --bmc1_ucm_relax_model                  4
% 3.20/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.00  --bmc1_ucm_layered_model                none
% 3.20/1.00  --bmc1_ucm_max_lemma_size               10
% 3.20/1.00  
% 3.20/1.00  ------ AIG Options
% 3.20/1.00  
% 3.20/1.00  --aig_mode                              false
% 3.20/1.00  
% 3.20/1.00  ------ Instantiation Options
% 3.20/1.00  
% 3.20/1.00  --instantiation_flag                    true
% 3.20/1.00  --inst_sos_flag                         false
% 3.20/1.00  --inst_sos_phase                        true
% 3.20/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.00  --inst_lit_sel_side                     num_symb
% 3.20/1.00  --inst_solver_per_active                1400
% 3.20/1.00  --inst_solver_calls_frac                1.
% 3.20/1.00  --inst_passive_queue_type               priority_queues
% 3.20/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.00  --inst_passive_queues_freq              [25;2]
% 3.20/1.00  --inst_dismatching                      true
% 3.20/1.00  --inst_eager_unprocessed_to_passive     true
% 3.20/1.00  --inst_prop_sim_given                   true
% 3.20/1.00  --inst_prop_sim_new                     false
% 3.20/1.00  --inst_subs_new                         false
% 3.20/1.00  --inst_eq_res_simp                      false
% 3.20/1.00  --inst_subs_given                       false
% 3.20/1.00  --inst_orphan_elimination               true
% 3.20/1.00  --inst_learning_loop_flag               true
% 3.20/1.00  --inst_learning_start                   3000
% 3.20/1.00  --inst_learning_factor                  2
% 3.20/1.00  --inst_start_prop_sim_after_learn       3
% 3.20/1.00  --inst_sel_renew                        solver
% 3.20/1.00  --inst_lit_activity_flag                true
% 3.20/1.00  --inst_restr_to_given                   false
% 3.20/1.00  --inst_activity_threshold               500
% 3.20/1.00  --inst_out_proof                        true
% 3.20/1.00  
% 3.20/1.00  ------ Resolution Options
% 3.20/1.00  
% 3.20/1.00  --resolution_flag                       true
% 3.20/1.00  --res_lit_sel                           adaptive
% 3.20/1.00  --res_lit_sel_side                      none
% 3.20/1.00  --res_ordering                          kbo
% 3.20/1.00  --res_to_prop_solver                    active
% 3.20/1.00  --res_prop_simpl_new                    false
% 3.20/1.00  --res_prop_simpl_given                  true
% 3.20/1.00  --res_passive_queue_type                priority_queues
% 3.20/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.00  --res_passive_queues_freq               [15;5]
% 3.20/1.00  --res_forward_subs                      full
% 3.20/1.00  --res_backward_subs                     full
% 3.20/1.00  --res_forward_subs_resolution           true
% 3.20/1.00  --res_backward_subs_resolution          true
% 3.20/1.00  --res_orphan_elimination                true
% 3.20/1.00  --res_time_limit                        2.
% 3.20/1.00  --res_out_proof                         true
% 3.20/1.00  
% 3.20/1.00  ------ Superposition Options
% 3.20/1.00  
% 3.20/1.00  --superposition_flag                    true
% 3.20/1.00  --sup_passive_queue_type                priority_queues
% 3.20/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.00  --demod_completeness_check              fast
% 3.20/1.00  --demod_use_ground                      true
% 3.20/1.00  --sup_to_prop_solver                    passive
% 3.20/1.00  --sup_prop_simpl_new                    true
% 3.20/1.00  --sup_prop_simpl_given                  true
% 3.20/1.00  --sup_fun_splitting                     false
% 3.20/1.00  --sup_smt_interval                      50000
% 3.20/1.00  
% 3.20/1.00  ------ Superposition Simplification Setup
% 3.20/1.00  
% 3.20/1.00  --sup_indices_passive                   []
% 3.20/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_full_bw                           [BwDemod]
% 3.20/1.00  --sup_immed_triv                        [TrivRules]
% 3.20/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_immed_bw_main                     []
% 3.20/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.00  
% 3.20/1.00  ------ Combination Options
% 3.20/1.00  
% 3.20/1.00  --comb_res_mult                         3
% 3.20/1.00  --comb_sup_mult                         2
% 3.20/1.00  --comb_inst_mult                        10
% 3.20/1.00  
% 3.20/1.00  ------ Debug Options
% 3.20/1.00  
% 3.20/1.00  --dbg_backtrace                         false
% 3.20/1.00  --dbg_dump_prop_clauses                 false
% 3.20/1.00  --dbg_dump_prop_clauses_file            -
% 3.20/1.00  --dbg_out_stat                          false
% 3.20/1.00  ------ Parsing...
% 3.20/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/1.00  ------ Proving...
% 3.20/1.00  ------ Problem Properties 
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  clauses                                 25
% 3.20/1.00  conjectures                             2
% 3.20/1.00  EPR                                     2
% 3.20/1.00  Horn                                    18
% 3.20/1.00  unary                                   7
% 3.20/1.00  binary                                  11
% 3.20/1.00  lits                                    51
% 3.20/1.00  lits eq                                 19
% 3.20/1.00  fd_pure                                 0
% 3.20/1.00  fd_pseudo                               0
% 3.20/1.00  fd_cond                                 1
% 3.20/1.00  fd_pseudo_cond                          6
% 3.20/1.00  AC symbols                              0
% 3.20/1.00  
% 3.20/1.00  ------ Schedule dynamic 5 is on 
% 3.20/1.00  
% 3.20/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  ------ 
% 3.20/1.00  Current options:
% 3.20/1.00  ------ 
% 3.20/1.00  
% 3.20/1.00  ------ Input Options
% 3.20/1.00  
% 3.20/1.00  --out_options                           all
% 3.20/1.00  --tptp_safe_out                         true
% 3.20/1.00  --problem_path                          ""
% 3.20/1.00  --include_path                          ""
% 3.20/1.00  --clausifier                            res/vclausify_rel
% 3.20/1.00  --clausifier_options                    --mode clausify
% 3.20/1.00  --stdin                                 false
% 3.20/1.00  --stats_out                             all
% 3.20/1.00  
% 3.20/1.00  ------ General Options
% 3.20/1.00  
% 3.20/1.00  --fof                                   false
% 3.20/1.00  --time_out_real                         305.
% 3.20/1.00  --time_out_virtual                      -1.
% 3.20/1.00  --symbol_type_check                     false
% 3.20/1.00  --clausify_out                          false
% 3.20/1.00  --sig_cnt_out                           false
% 3.20/1.00  --trig_cnt_out                          false
% 3.20/1.00  --trig_cnt_out_tolerance                1.
% 3.20/1.00  --trig_cnt_out_sk_spl                   false
% 3.20/1.00  --abstr_cl_out                          false
% 3.20/1.00  
% 3.20/1.00  ------ Global Options
% 3.20/1.00  
% 3.20/1.00  --schedule                              default
% 3.20/1.00  --add_important_lit                     false
% 3.20/1.00  --prop_solver_per_cl                    1000
% 3.20/1.00  --min_unsat_core                        false
% 3.20/1.00  --soft_assumptions                      false
% 3.20/1.00  --soft_lemma_size                       3
% 3.20/1.00  --prop_impl_unit_size                   0
% 3.20/1.00  --prop_impl_unit                        []
% 3.20/1.00  --share_sel_clauses                     true
% 3.20/1.00  --reset_solvers                         false
% 3.20/1.00  --bc_imp_inh                            [conj_cone]
% 3.20/1.00  --conj_cone_tolerance                   3.
% 3.20/1.00  --extra_neg_conj                        none
% 3.20/1.00  --large_theory_mode                     true
% 3.20/1.00  --prolific_symb_bound                   200
% 3.20/1.00  --lt_threshold                          2000
% 3.20/1.00  --clause_weak_htbl                      true
% 3.20/1.00  --gc_record_bc_elim                     false
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing Options
% 3.20/1.00  
% 3.20/1.00  --preprocessing_flag                    true
% 3.20/1.00  --time_out_prep_mult                    0.1
% 3.20/1.00  --splitting_mode                        input
% 3.20/1.00  --splitting_grd                         true
% 3.20/1.00  --splitting_cvd                         false
% 3.20/1.00  --splitting_cvd_svl                     false
% 3.20/1.00  --splitting_nvd                         32
% 3.20/1.00  --sub_typing                            true
% 3.20/1.00  --prep_gs_sim                           true
% 3.20/1.00  --prep_unflatten                        true
% 3.20/1.00  --prep_res_sim                          true
% 3.20/1.00  --prep_upred                            true
% 3.20/1.00  --prep_sem_filter                       exhaustive
% 3.20/1.00  --prep_sem_filter_out                   false
% 3.20/1.00  --pred_elim                             true
% 3.20/1.00  --res_sim_input                         true
% 3.20/1.00  --eq_ax_congr_red                       true
% 3.20/1.00  --pure_diseq_elim                       true
% 3.20/1.00  --brand_transform                       false
% 3.20/1.00  --non_eq_to_eq                          false
% 3.20/1.00  --prep_def_merge                        true
% 3.20/1.00  --prep_def_merge_prop_impl              false
% 3.20/1.00  --prep_def_merge_mbd                    true
% 3.20/1.00  --prep_def_merge_tr_red                 false
% 3.20/1.00  --prep_def_merge_tr_cl                  false
% 3.20/1.00  --smt_preprocessing                     true
% 3.20/1.00  --smt_ac_axioms                         fast
% 3.20/1.00  --preprocessed_out                      false
% 3.20/1.00  --preprocessed_stats                    false
% 3.20/1.00  
% 3.20/1.00  ------ Abstraction refinement Options
% 3.20/1.00  
% 3.20/1.00  --abstr_ref                             []
% 3.20/1.00  --abstr_ref_prep                        false
% 3.20/1.00  --abstr_ref_until_sat                   false
% 3.20/1.00  --abstr_ref_sig_restrict                funpre
% 3.20/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.00  --abstr_ref_under                       []
% 3.20/1.00  
% 3.20/1.00  ------ SAT Options
% 3.20/1.00  
% 3.20/1.00  --sat_mode                              false
% 3.20/1.00  --sat_fm_restart_options                ""
% 3.20/1.00  --sat_gr_def                            false
% 3.20/1.00  --sat_epr_types                         true
% 3.20/1.00  --sat_non_cyclic_types                  false
% 3.20/1.00  --sat_finite_models                     false
% 3.20/1.00  --sat_fm_lemmas                         false
% 3.20/1.00  --sat_fm_prep                           false
% 3.20/1.00  --sat_fm_uc_incr                        true
% 3.20/1.00  --sat_out_model                         small
% 3.20/1.00  --sat_out_clauses                       false
% 3.20/1.00  
% 3.20/1.00  ------ QBF Options
% 3.20/1.00  
% 3.20/1.00  --qbf_mode                              false
% 3.20/1.00  --qbf_elim_univ                         false
% 3.20/1.00  --qbf_dom_inst                          none
% 3.20/1.00  --qbf_dom_pre_inst                      false
% 3.20/1.00  --qbf_sk_in                             false
% 3.20/1.00  --qbf_pred_elim                         true
% 3.20/1.00  --qbf_split                             512
% 3.20/1.00  
% 3.20/1.00  ------ BMC1 Options
% 3.20/1.00  
% 3.20/1.00  --bmc1_incremental                      false
% 3.20/1.00  --bmc1_axioms                           reachable_all
% 3.20/1.00  --bmc1_min_bound                        0
% 3.20/1.00  --bmc1_max_bound                        -1
% 3.20/1.00  --bmc1_max_bound_default                -1
% 3.20/1.00  --bmc1_symbol_reachability              true
% 3.20/1.00  --bmc1_property_lemmas                  false
% 3.20/1.00  --bmc1_k_induction                      false
% 3.20/1.00  --bmc1_non_equiv_states                 false
% 3.20/1.00  --bmc1_deadlock                         false
% 3.20/1.00  --bmc1_ucm                              false
% 3.20/1.00  --bmc1_add_unsat_core                   none
% 3.20/1.00  --bmc1_unsat_core_children              false
% 3.20/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.00  --bmc1_out_stat                         full
% 3.20/1.00  --bmc1_ground_init                      false
% 3.20/1.00  --bmc1_pre_inst_next_state              false
% 3.20/1.00  --bmc1_pre_inst_state                   false
% 3.20/1.00  --bmc1_pre_inst_reach_state             false
% 3.20/1.00  --bmc1_out_unsat_core                   false
% 3.20/1.00  --bmc1_aig_witness_out                  false
% 3.20/1.00  --bmc1_verbose                          false
% 3.20/1.00  --bmc1_dump_clauses_tptp                false
% 3.20/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.00  --bmc1_dump_file                        -
% 3.20/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.00  --bmc1_ucm_extend_mode                  1
% 3.20/1.00  --bmc1_ucm_init_mode                    2
% 3.20/1.00  --bmc1_ucm_cone_mode                    none
% 3.20/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.00  --bmc1_ucm_relax_model                  4
% 3.20/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.00  --bmc1_ucm_layered_model                none
% 3.20/1.00  --bmc1_ucm_max_lemma_size               10
% 3.20/1.00  
% 3.20/1.00  ------ AIG Options
% 3.20/1.00  
% 3.20/1.00  --aig_mode                              false
% 3.20/1.00  
% 3.20/1.00  ------ Instantiation Options
% 3.20/1.00  
% 3.20/1.00  --instantiation_flag                    true
% 3.20/1.00  --inst_sos_flag                         false
% 3.20/1.00  --inst_sos_phase                        true
% 3.20/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.00  --inst_lit_sel_side                     none
% 3.20/1.00  --inst_solver_per_active                1400
% 3.20/1.00  --inst_solver_calls_frac                1.
% 3.20/1.00  --inst_passive_queue_type               priority_queues
% 3.20/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.00  --inst_passive_queues_freq              [25;2]
% 3.20/1.00  --inst_dismatching                      true
% 3.20/1.00  --inst_eager_unprocessed_to_passive     true
% 3.20/1.00  --inst_prop_sim_given                   true
% 3.20/1.00  --inst_prop_sim_new                     false
% 3.20/1.00  --inst_subs_new                         false
% 3.20/1.00  --inst_eq_res_simp                      false
% 3.20/1.00  --inst_subs_given                       false
% 3.20/1.00  --inst_orphan_elimination               true
% 3.20/1.00  --inst_learning_loop_flag               true
% 3.20/1.00  --inst_learning_start                   3000
% 3.20/1.00  --inst_learning_factor                  2
% 3.20/1.00  --inst_start_prop_sim_after_learn       3
% 3.20/1.00  --inst_sel_renew                        solver
% 3.20/1.00  --inst_lit_activity_flag                true
% 3.20/1.00  --inst_restr_to_given                   false
% 3.20/1.00  --inst_activity_threshold               500
% 3.20/1.00  --inst_out_proof                        true
% 3.20/1.00  
% 3.20/1.00  ------ Resolution Options
% 3.20/1.00  
% 3.20/1.00  --resolution_flag                       false
% 3.20/1.00  --res_lit_sel                           adaptive
% 3.20/1.00  --res_lit_sel_side                      none
% 3.20/1.00  --res_ordering                          kbo
% 3.20/1.00  --res_to_prop_solver                    active
% 3.20/1.00  --res_prop_simpl_new                    false
% 3.20/1.00  --res_prop_simpl_given                  true
% 3.20/1.00  --res_passive_queue_type                priority_queues
% 3.20/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.00  --res_passive_queues_freq               [15;5]
% 3.20/1.00  --res_forward_subs                      full
% 3.20/1.00  --res_backward_subs                     full
% 3.20/1.00  --res_forward_subs_resolution           true
% 3.20/1.00  --res_backward_subs_resolution          true
% 3.20/1.00  --res_orphan_elimination                true
% 3.20/1.00  --res_time_limit                        2.
% 3.20/1.00  --res_out_proof                         true
% 3.20/1.00  
% 3.20/1.00  ------ Superposition Options
% 3.20/1.00  
% 3.20/1.00  --superposition_flag                    true
% 3.20/1.00  --sup_passive_queue_type                priority_queues
% 3.20/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.00  --demod_completeness_check              fast
% 3.20/1.00  --demod_use_ground                      true
% 3.20/1.00  --sup_to_prop_solver                    passive
% 3.20/1.00  --sup_prop_simpl_new                    true
% 3.20/1.00  --sup_prop_simpl_given                  true
% 3.20/1.00  --sup_fun_splitting                     false
% 3.20/1.00  --sup_smt_interval                      50000
% 3.20/1.00  
% 3.20/1.00  ------ Superposition Simplification Setup
% 3.20/1.00  
% 3.20/1.00  --sup_indices_passive                   []
% 3.20/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_full_bw                           [BwDemod]
% 3.20/1.00  --sup_immed_triv                        [TrivRules]
% 3.20/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_immed_bw_main                     []
% 3.20/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.00  
% 3.20/1.00  ------ Combination Options
% 3.20/1.00  
% 3.20/1.00  --comb_res_mult                         3
% 3.20/1.00  --comb_sup_mult                         2
% 3.20/1.00  --comb_inst_mult                        10
% 3.20/1.00  
% 3.20/1.00  ------ Debug Options
% 3.20/1.00  
% 3.20/1.00  --dbg_backtrace                         false
% 3.20/1.00  --dbg_dump_prop_clauses                 false
% 3.20/1.00  --dbg_dump_prop_clauses_file            -
% 3.20/1.00  --dbg_out_stat                          false
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  ------ Proving...
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  % SZS status Theorem for theBenchmark.p
% 3.20/1.00  
% 3.20/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/1.00  
% 3.20/1.00  fof(f2,axiom,(
% 3.20/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f19,plain,(
% 3.20/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.20/1.00    inference(ennf_transformation,[],[f2])).
% 3.20/1.00  
% 3.20/1.00  fof(f29,plain,(
% 3.20/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.20/1.00    introduced(choice_axiom,[])).
% 3.20/1.00  
% 3.20/1.00  fof(f30,plain,(
% 3.20/1.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f29])).
% 3.20/1.00  
% 3.20/1.00  fof(f48,plain,(
% 3.20/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.20/1.00    inference(cnf_transformation,[],[f30])).
% 3.20/1.00  
% 3.20/1.00  fof(f13,axiom,(
% 3.20/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f22,plain,(
% 3.20/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/1.00    inference(ennf_transformation,[],[f13])).
% 3.20/1.00  
% 3.20/1.00  fof(f67,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f22])).
% 3.20/1.00  
% 3.20/1.00  fof(f4,axiom,(
% 3.20/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f52,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f4])).
% 3.20/1.00  
% 3.20/1.00  fof(f83,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.20/1.00    inference(definition_unfolding,[],[f67,f52])).
% 3.20/1.00  
% 3.20/1.00  fof(f17,conjecture,(
% 3.20/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f18,negated_conjecture,(
% 3.20/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.20/1.00    inference(negated_conjecture,[],[f17])).
% 3.20/1.00  
% 3.20/1.00  fof(f23,plain,(
% 3.20/1.00    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/1.00    inference(ennf_transformation,[],[f18])).
% 3.20/1.00  
% 3.20/1.00  fof(f38,plain,(
% 3.20/1.00    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/1.00    inference(nnf_transformation,[],[f23])).
% 3.20/1.00  
% 3.20/1.00  fof(f39,plain,(
% 3.20/1.00    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/1.00    inference(flattening,[],[f38])).
% 3.20/1.00  
% 3.20/1.00  fof(f40,plain,(
% 3.20/1.00    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK3) != sK4 | ~r1_tarski(sK4,k3_subset_1(sK3,sK4))) & (k1_subset_1(sK3) = sK4 | r1_tarski(sK4,k3_subset_1(sK3,sK4))) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 3.20/1.00    introduced(choice_axiom,[])).
% 3.20/1.00  
% 3.20/1.00  fof(f41,plain,(
% 3.20/1.00    (k1_subset_1(sK3) != sK4 | ~r1_tarski(sK4,k3_subset_1(sK3,sK4))) & (k1_subset_1(sK3) = sK4 | r1_tarski(sK4,k3_subset_1(sK3,sK4))) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 3.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f40])).
% 3.20/1.00  
% 3.20/1.00  fof(f71,plain,(
% 3.20/1.00    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 3.20/1.00    inference(cnf_transformation,[],[f41])).
% 3.20/1.00  
% 3.20/1.00  fof(f1,axiom,(
% 3.20/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f24,plain,(
% 3.20/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.20/1.00    inference(nnf_transformation,[],[f1])).
% 3.20/1.00  
% 3.20/1.00  fof(f25,plain,(
% 3.20/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.20/1.00    inference(flattening,[],[f24])).
% 3.20/1.00  
% 3.20/1.00  fof(f26,plain,(
% 3.20/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.20/1.00    inference(rectify,[],[f25])).
% 3.20/1.00  
% 3.20/1.00  fof(f27,plain,(
% 3.20/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.20/1.00    introduced(choice_axiom,[])).
% 3.20/1.00  
% 3.20/1.00  fof(f28,plain,(
% 3.20/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.20/1.00  
% 3.20/1.00  fof(f44,plain,(
% 3.20/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.20/1.00    inference(cnf_transformation,[],[f28])).
% 3.20/1.00  
% 3.20/1.00  fof(f79,plain,(
% 3.20/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.20/1.00    inference(definition_unfolding,[],[f44,f52])).
% 3.20/1.00  
% 3.20/1.00  fof(f86,plain,(
% 3.20/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.20/1.00    inference(equality_resolution,[],[f79])).
% 3.20/1.00  
% 3.20/1.00  fof(f43,plain,(
% 3.20/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.20/1.00    inference(cnf_transformation,[],[f28])).
% 3.20/1.00  
% 3.20/1.00  fof(f80,plain,(
% 3.20/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.20/1.00    inference(definition_unfolding,[],[f43,f52])).
% 3.20/1.00  
% 3.20/1.00  fof(f87,plain,(
% 3.20/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.20/1.00    inference(equality_resolution,[],[f80])).
% 3.20/1.00  
% 3.20/1.00  fof(f6,axiom,(
% 3.20/1.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f54,plain,(
% 3.20/1.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f6])).
% 3.20/1.00  
% 3.20/1.00  fof(f8,axiom,(
% 3.20/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f56,plain,(
% 3.20/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.20/1.00    inference(cnf_transformation,[],[f8])).
% 3.20/1.00  
% 3.20/1.00  fof(f7,axiom,(
% 3.20/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f55,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f7])).
% 3.20/1.00  
% 3.20/1.00  fof(f75,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.20/1.00    inference(definition_unfolding,[],[f55,f52,f52])).
% 3.20/1.00  
% 3.20/1.00  fof(f42,plain,(
% 3.20/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.20/1.00    inference(cnf_transformation,[],[f28])).
% 3.20/1.00  
% 3.20/1.00  fof(f81,plain,(
% 3.20/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.20/1.00    inference(definition_unfolding,[],[f42,f52])).
% 3.20/1.00  
% 3.20/1.00  fof(f88,plain,(
% 3.20/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.20/1.00    inference(equality_resolution,[],[f81])).
% 3.20/1.00  
% 3.20/1.00  fof(f72,plain,(
% 3.20/1.00    k1_subset_1(sK3) = sK4 | r1_tarski(sK4,k3_subset_1(sK3,sK4))),
% 3.20/1.00    inference(cnf_transformation,[],[f41])).
% 3.20/1.00  
% 3.20/1.00  fof(f11,axiom,(
% 3.20/1.00    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f65,plain,(
% 3.20/1.00    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f11])).
% 3.20/1.00  
% 3.20/1.00  fof(f85,plain,(
% 3.20/1.00    k1_xboole_0 = sK4 | r1_tarski(sK4,k3_subset_1(sK3,sK4))),
% 3.20/1.00    inference(definition_unfolding,[],[f72,f65])).
% 3.20/1.00  
% 3.20/1.00  fof(f5,axiom,(
% 3.20/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f20,plain,(
% 3.20/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.20/1.00    inference(ennf_transformation,[],[f5])).
% 3.20/1.00  
% 3.20/1.00  fof(f53,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f20])).
% 3.20/1.00  
% 3.20/1.00  fof(f73,plain,(
% 3.20/1.00    k1_subset_1(sK3) != sK4 | ~r1_tarski(sK4,k3_subset_1(sK3,sK4))),
% 3.20/1.00    inference(cnf_transformation,[],[f41])).
% 3.20/1.00  
% 3.20/1.00  fof(f84,plain,(
% 3.20/1.00    k1_xboole_0 != sK4 | ~r1_tarski(sK4,k3_subset_1(sK3,sK4))),
% 3.20/1.00    inference(definition_unfolding,[],[f73,f65])).
% 3.20/1.00  
% 3.20/1.00  fof(f3,axiom,(
% 3.20/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f31,plain,(
% 3.20/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/1.00    inference(nnf_transformation,[],[f3])).
% 3.20/1.00  
% 3.20/1.00  fof(f32,plain,(
% 3.20/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/1.00    inference(flattening,[],[f31])).
% 3.20/1.00  
% 3.20/1.00  fof(f49,plain,(
% 3.20/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.20/1.00    inference(cnf_transformation,[],[f32])).
% 3.20/1.00  
% 3.20/1.00  fof(f90,plain,(
% 3.20/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.20/1.00    inference(equality_resolution,[],[f49])).
% 3.20/1.00  
% 3.20/1.00  fof(f51,plain,(
% 3.20/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f32])).
% 3.20/1.00  
% 3.20/1.00  fof(f9,axiom,(
% 3.20/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f33,plain,(
% 3.20/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.20/1.00    inference(nnf_transformation,[],[f9])).
% 3.20/1.00  
% 3.20/1.00  fof(f34,plain,(
% 3.20/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.20/1.00    inference(rectify,[],[f33])).
% 3.20/1.00  
% 3.20/1.00  fof(f35,plain,(
% 3.20/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.20/1.00    introduced(choice_axiom,[])).
% 3.20/1.00  
% 3.20/1.00  fof(f36,plain,(
% 3.20/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 3.20/1.00  
% 3.20/1.00  fof(f57,plain,(
% 3.20/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.20/1.00    inference(cnf_transformation,[],[f36])).
% 3.20/1.00  
% 3.20/1.00  fof(f92,plain,(
% 3.20/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.20/1.00    inference(equality_resolution,[],[f57])).
% 3.20/1.00  
% 3.20/1.00  fof(f10,axiom,(
% 3.20/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f21,plain,(
% 3.20/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.20/1.00    inference(ennf_transformation,[],[f10])).
% 3.20/1.00  
% 3.20/1.00  fof(f37,plain,(
% 3.20/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.20/1.00    inference(nnf_transformation,[],[f21])).
% 3.20/1.00  
% 3.20/1.00  fof(f61,plain,(
% 3.20/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f37])).
% 3.20/1.00  
% 3.20/1.00  fof(f16,axiom,(
% 3.20/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f70,plain,(
% 3.20/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f16])).
% 3.20/1.00  
% 3.20/1.00  fof(f14,axiom,(
% 3.20/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f68,plain,(
% 3.20/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f14])).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7,plain,
% 3.20/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1089,plain,
% 3.20/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_23,plain,
% 3.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.20/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.20/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_28,negated_conjecture,
% 3.20/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 3.20/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_403,plain,
% 3.20/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.20/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 3.20/1.00      | sK4 != X1 ),
% 3.20/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_404,plain,
% 3.20/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
% 3.20/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 3.20/1.00      inference(unflattening,[status(thm)],[c_403]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1242,plain,
% 3.20/1.00      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
% 3.20/1.00      inference(equality_resolution,[status(thm)],[c_404]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4,plain,
% 3.20/1.00      ( ~ r2_hidden(X0,X1)
% 3.20/1.00      | r2_hidden(X0,X2)
% 3.20/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.20/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1092,plain,
% 3.20/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.20/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.20/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7831,plain,
% 3.20/1.00      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
% 3.20/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.20/1.00      | r2_hidden(X0,sK4) = iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_1242,c_1092]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_5,plain,
% 3.20/1.00      ( ~ r2_hidden(X0,X1)
% 3.20/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.20/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1091,plain,
% 3.20/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.20/1.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4262,plain,
% 3.20/1.00      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
% 3.20/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_1242,c_1091]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_12,plain,
% 3.20/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4275,plain,
% 3.20/1.00      ( r2_hidden(X0,k5_xboole_0(X1,k1_xboole_0)) != iProver_top
% 3.20/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_12,c_1091]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_13,plain,
% 3.20/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4302,plain,
% 3.20/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.20/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_4275,c_13]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_0,plain,
% 3.20/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.20/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_6,plain,
% 3.20/1.00      ( r2_hidden(X0,X1)
% 3.20/1.00      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.20/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1090,plain,
% 3.20/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.20/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2909,plain,
% 3.20/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.20/1.00      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_0,c_1090]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_3043,plain,
% 3.20/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.20/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_12,c_2909]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4518,plain,
% 3.20/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.20/1.00      inference(global_propositional_subsumption,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_4302,c_3043]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1370,plain,
% 3.20/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1375,plain,
% 3.20/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 3.20/1.00      inference(light_normalisation,[status(thm)],[c_1370,c_12,c_13]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1444,plain,
% 3.20/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_1375,c_0]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1446,plain,
% 3.20/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.20/1.00      inference(light_normalisation,[status(thm)],[c_1444,c_12,c_13]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1447,plain,
% 3.20/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_1446,c_1375]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_27,negated_conjecture,
% 3.20/1.00      ( r1_tarski(sK4,k3_subset_1(sK3,sK4)) | k1_xboole_0 = sK4 ),
% 3.20/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1080,plain,
% 3.20/1.00      ( k1_xboole_0 = sK4
% 3.20/1.00      | r1_tarski(sK4,k3_subset_1(sK3,sK4)) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_11,plain,
% 3.20/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1086,plain,
% 3.20/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1973,plain,
% 3.20/1.00      ( k3_xboole_0(sK4,k3_subset_1(sK3,sK4)) = sK4 | sK4 = k1_xboole_0 ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_1080,c_1086]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2100,plain,
% 3.20/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,sK4))) = k3_xboole_0(sK4,k3_subset_1(sK3,sK4))
% 3.20/1.00      | sK4 = k1_xboole_0 ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_1973,c_0]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2103,plain,
% 3.20/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK3,sK4)))) = k3_xboole_0(sK4,k5_xboole_0(sK4,sK4))
% 3.20/1.00      | sK4 = k1_xboole_0 ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_2100,c_0]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_6926,plain,
% 3.20/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK3,sK4)))) = k3_xboole_0(sK4,k1_xboole_0)
% 3.20/1.00      | sK4 = k1_xboole_0 ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_1447,c_2103]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1371,plain,
% 3.20/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_6933,plain,
% 3.20/1.00      ( k3_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK3,sK4)))) = k1_xboole_0
% 3.20/1.00      | sK4 = k1_xboole_0 ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_6926,c_12,c_1371]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_26,negated_conjecture,
% 3.20/1.00      ( ~ r1_tarski(sK4,k3_subset_1(sK3,sK4)) | k1_xboole_0 != sK4 ),
% 3.20/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_10,plain,
% 3.20/1.00      ( r1_tarski(X0,X0) ),
% 3.20/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_68,plain,
% 3.20/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8,plain,
% 3.20/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.20/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_72,plain,
% 3.20/1.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.20/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_619,plain,
% 3.20/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.20/1.00      theory(equality) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1283,plain,
% 3.20/1.00      ( ~ r1_tarski(X0,X1)
% 3.20/1.00      | r1_tarski(sK4,k3_subset_1(sK3,sK4))
% 3.20/1.00      | k3_subset_1(sK3,sK4) != X1
% 3.20/1.00      | sK4 != X0 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_619]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1412,plain,
% 3.20/1.00      ( ~ r1_tarski(X0,k3_subset_1(sK3,sK4))
% 3.20/1.00      | r1_tarski(sK4,k3_subset_1(sK3,sK4))
% 3.20/1.00      | k3_subset_1(sK3,sK4) != k3_subset_1(sK3,sK4)
% 3.20/1.00      | sK4 != X0 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_1283]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1415,plain,
% 3.20/1.00      ( r1_tarski(sK4,k3_subset_1(sK3,sK4))
% 3.20/1.00      | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK3,sK4))
% 3.20/1.00      | k3_subset_1(sK3,sK4) != k3_subset_1(sK3,sK4)
% 3.20/1.00      | sK4 != k1_xboole_0 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_1412]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_614,plain,( X0 = X0 ),theory(equality) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1413,plain,
% 3.20/1.00      ( k3_subset_1(sK3,sK4) = k3_subset_1(sK3,sK4) ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_614]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_615,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1459,plain,
% 3.20/1.00      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_615]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1460,plain,
% 3.20/1.00      ( sK4 != k1_xboole_0
% 3.20/1.00      | k1_xboole_0 = sK4
% 3.20/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_1459]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_17,plain,
% 3.20/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.20/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1501,plain,
% 3.20/1.00      ( r1_tarski(X0,k3_subset_1(sK3,sK4))
% 3.20/1.00      | ~ r2_hidden(X0,k1_zfmisc_1(k3_subset_1(sK3,sK4))) ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1503,plain,
% 3.20/1.00      ( r1_tarski(k1_xboole_0,k3_subset_1(sK3,sK4))
% 3.20/1.00      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_subset_1(sK3,sK4))) ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_1501]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_21,plain,
% 3.20/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.20/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_25,plain,
% 3.20/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.20/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_364,plain,
% 3.20/1.00      ( r2_hidden(X0,X1)
% 3.20/1.00      | v1_xboole_0(X1)
% 3.20/1.00      | k1_zfmisc_1(X2) != X1
% 3.20/1.00      | k1_xboole_0 != X0 ),
% 3.20/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_365,plain,
% 3.20/1.00      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
% 3.20/1.00      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.20/1.00      inference(unflattening,[status(thm)],[c_364]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_24,plain,
% 3.20/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.20/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_369,plain,
% 3.20/1.00      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.20/1.00      inference(global_propositional_subsumption,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_365,c_24]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7072,plain,
% 3.20/1.00      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_subset_1(sK3,sK4))) ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_369]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7122,plain,
% 3.20/1.00      ( k3_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK3,sK4)))) = k1_xboole_0 ),
% 3.20/1.00      inference(global_propositional_subsumption,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_6933,c_26,c_68,c_72,c_1415,c_1413,c_1460,c_1503,
% 3.20/1.00                 c_7072]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7131,plain,
% 3.20/1.00      ( k3_xboole_0(sK4,k3_subset_1(sK3,sK4)) = k5_xboole_0(sK4,k1_xboole_0) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_7122,c_0]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7149,plain,
% 3.20/1.00      ( k3_xboole_0(sK4,k3_subset_1(sK3,sK4)) = sK4 ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_7131,c_13]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7847,plain,
% 3.20/1.00      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
% 3.20/1.00      | r2_hidden(X0,k5_xboole_0(sK4,sK4)) = iProver_top
% 3.20/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_7149,c_1092]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7868,plain,
% 3.20/1.00      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
% 3.20/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.20/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_7847,c_1447]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8019,plain,
% 3.20/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.20/1.00      | r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top ),
% 3.20/1.00      inference(global_propositional_subsumption,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_7831,c_3043,c_4262,c_4302,c_7868]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8020,plain,
% 3.20/1.00      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
% 3.20/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.20/1.00      inference(renaming,[status(thm)],[c_8019]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8028,plain,
% 3.20/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.20/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_8020,c_4262]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8280,plain,
% 3.20/1.00      ( r2_hidden(X0,sK4) != iProver_top ),
% 3.20/1.00      inference(global_propositional_subsumption,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_8028,c_3043,c_4262,c_4302,c_7868]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8287,plain,
% 3.20/1.00      ( sK4 = k1_xboole_0 ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_1089,c_8280]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(contradiction,plain,
% 3.20/1.00      ( $false ),
% 3.20/1.00      inference(minisat,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_8287,c_7072,c_1503,c_1460,c_1413,c_1415,c_72,c_68,
% 3.20/1.00                 c_26]) ).
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/1.00  
% 3.20/1.00  ------                               Statistics
% 3.20/1.00  
% 3.20/1.00  ------ General
% 3.20/1.00  
% 3.20/1.00  abstr_ref_over_cycles:                  0
% 3.20/1.00  abstr_ref_under_cycles:                 0
% 3.20/1.00  gc_basic_clause_elim:                   0
% 3.20/1.00  forced_gc_time:                         0
% 3.20/1.00  parsing_time:                           0.007
% 3.20/1.00  unif_index_cands_time:                  0.
% 3.20/1.00  unif_index_add_time:                    0.
% 3.20/1.00  orderings_time:                         0.
% 3.20/1.00  out_proof_time:                         0.011
% 3.20/1.00  total_time:                             0.231
% 3.20/1.00  num_of_symbols:                         45
% 3.20/1.00  num_of_terms:                           8114
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing
% 3.20/1.00  
% 3.20/1.00  num_of_splits:                          0
% 3.20/1.00  num_of_split_atoms:                     0
% 3.20/1.00  num_of_reused_defs:                     0
% 3.20/1.00  num_eq_ax_congr_red:                    24
% 3.20/1.00  num_of_sem_filtered_clauses:            1
% 3.20/1.00  num_of_subtypes:                        0
% 3.20/1.00  monotx_restored_types:                  0
% 3.20/1.00  sat_num_of_epr_types:                   0
% 3.20/1.00  sat_num_of_non_cyclic_types:            0
% 3.20/1.00  sat_guarded_non_collapsed_types:        0
% 3.20/1.00  num_pure_diseq_elim:                    0
% 3.20/1.00  simp_replaced_by:                       0
% 3.20/1.00  res_preprocessed:                       120
% 3.20/1.00  prep_upred:                             0
% 3.20/1.00  prep_unflattend:                        14
% 3.20/1.00  smt_new_axioms:                         0
% 3.20/1.00  pred_elim_cands:                        2
% 3.20/1.00  pred_elim:                              2
% 3.20/1.00  pred_elim_cl:                           3
% 3.20/1.00  pred_elim_cycles:                       4
% 3.20/1.00  merged_defs:                            16
% 3.20/1.00  merged_defs_ncl:                        0
% 3.20/1.00  bin_hyper_res:                          17
% 3.20/1.00  prep_cycles:                            4
% 3.20/1.00  pred_elim_time:                         0.001
% 3.20/1.00  splitting_time:                         0.
% 3.20/1.00  sem_filter_time:                        0.
% 3.20/1.00  monotx_time:                            0.
% 3.20/1.00  subtype_inf_time:                       0.
% 3.20/1.00  
% 3.20/1.00  ------ Problem properties
% 3.20/1.00  
% 3.20/1.00  clauses:                                25
% 3.20/1.00  conjectures:                            2
% 3.20/1.00  epr:                                    2
% 3.20/1.00  horn:                                   18
% 3.20/1.00  ground:                                 3
% 3.20/1.00  unary:                                  7
% 3.20/1.00  binary:                                 11
% 3.20/1.00  lits:                                   51
% 3.20/1.00  lits_eq:                                19
% 3.20/1.00  fd_pure:                                0
% 3.20/1.00  fd_pseudo:                              0
% 3.20/1.00  fd_cond:                                1
% 3.20/1.00  fd_pseudo_cond:                         6
% 3.20/1.00  ac_symbols:                             0
% 3.20/1.00  
% 3.20/1.00  ------ Propositional Solver
% 3.20/1.00  
% 3.20/1.00  prop_solver_calls:                      29
% 3.20/1.00  prop_fast_solver_calls:                 754
% 3.20/1.00  smt_solver_calls:                       0
% 3.20/1.00  smt_fast_solver_calls:                  0
% 3.20/1.00  prop_num_of_clauses:                    2977
% 3.20/1.00  prop_preprocess_simplified:             7494
% 3.20/1.00  prop_fo_subsumed:                       17
% 3.20/1.00  prop_solver_time:                       0.
% 3.20/1.00  smt_solver_time:                        0.
% 3.20/1.00  smt_fast_solver_time:                   0.
% 3.20/1.00  prop_fast_solver_time:                  0.
% 3.20/1.00  prop_unsat_core_time:                   0.
% 3.20/1.00  
% 3.20/1.00  ------ QBF
% 3.20/1.00  
% 3.20/1.00  qbf_q_res:                              0
% 3.20/1.00  qbf_num_tautologies:                    0
% 3.20/1.00  qbf_prep_cycles:                        0
% 3.20/1.00  
% 3.20/1.00  ------ BMC1
% 3.20/1.00  
% 3.20/1.00  bmc1_current_bound:                     -1
% 3.20/1.00  bmc1_last_solved_bound:                 -1
% 3.20/1.00  bmc1_unsat_core_size:                   -1
% 3.20/1.00  bmc1_unsat_core_parents_size:           -1
% 3.20/1.00  bmc1_merge_next_fun:                    0
% 3.20/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.20/1.00  
% 3.20/1.00  ------ Instantiation
% 3.20/1.00  
% 3.20/1.00  inst_num_of_clauses:                    799
% 3.20/1.00  inst_num_in_passive:                    356
% 3.20/1.00  inst_num_in_active:                     270
% 3.20/1.00  inst_num_in_unprocessed:                173
% 3.20/1.00  inst_num_of_loops:                      430
% 3.20/1.00  inst_num_of_learning_restarts:          0
% 3.20/1.00  inst_num_moves_active_passive:          157
% 3.20/1.00  inst_lit_activity:                      0
% 3.20/1.00  inst_lit_activity_moves:                0
% 3.20/1.00  inst_num_tautologies:                   0
% 3.20/1.00  inst_num_prop_implied:                  0
% 3.20/1.00  inst_num_existing_simplified:           0
% 3.20/1.00  inst_num_eq_res_simplified:             0
% 3.20/1.00  inst_num_child_elim:                    0
% 3.20/1.00  inst_num_of_dismatching_blockings:      459
% 3.20/1.00  inst_num_of_non_proper_insts:           816
% 3.20/1.00  inst_num_of_duplicates:                 0
% 3.20/1.00  inst_inst_num_from_inst_to_res:         0
% 3.20/1.00  inst_dismatching_checking_time:         0.
% 3.20/1.00  
% 3.20/1.00  ------ Resolution
% 3.20/1.00  
% 3.20/1.00  res_num_of_clauses:                     0
% 3.20/1.00  res_num_in_passive:                     0
% 3.20/1.00  res_num_in_active:                      0
% 3.20/1.00  res_num_of_loops:                       124
% 3.20/1.00  res_forward_subset_subsumed:            59
% 3.20/1.00  res_backward_subset_subsumed:           0
% 3.20/1.00  res_forward_subsumed:                   2
% 3.20/1.00  res_backward_subsumed:                  0
% 3.20/1.00  res_forward_subsumption_resolution:     2
% 3.20/1.00  res_backward_subsumption_resolution:    0
% 3.20/1.00  res_clause_to_clause_subsumption:       623
% 3.20/1.00  res_orphan_elimination:                 0
% 3.20/1.00  res_tautology_del:                      119
% 3.20/1.00  res_num_eq_res_simplified:              0
% 3.20/1.00  res_num_sel_changes:                    0
% 3.20/1.00  res_moves_from_active_to_pass:          0
% 3.20/1.00  
% 3.20/1.00  ------ Superposition
% 3.20/1.00  
% 3.20/1.00  sup_time_total:                         0.
% 3.20/1.00  sup_time_generating:                    0.
% 3.20/1.00  sup_time_sim_full:                      0.
% 3.20/1.00  sup_time_sim_immed:                     0.
% 3.20/1.00  
% 3.20/1.00  sup_num_of_clauses:                     171
% 3.20/1.00  sup_num_in_active:                      64
% 3.20/1.00  sup_num_in_passive:                     107
% 3.20/1.00  sup_num_of_loops:                       85
% 3.20/1.00  sup_fw_superposition:                   201
% 3.20/1.00  sup_bw_superposition:                   134
% 3.20/1.00  sup_immediate_simplified:               128
% 3.20/1.00  sup_given_eliminated:                   3
% 3.20/1.00  comparisons_done:                       0
% 3.20/1.00  comparisons_avoided:                    42
% 3.20/1.00  
% 3.20/1.00  ------ Simplifications
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  sim_fw_subset_subsumed:                 6
% 3.20/1.00  sim_bw_subset_subsumed:                 21
% 3.20/1.00  sim_fw_subsumed:                        24
% 3.20/1.00  sim_bw_subsumed:                        14
% 3.20/1.00  sim_fw_subsumption_res:                 0
% 3.20/1.00  sim_bw_subsumption_res:                 0
% 3.20/1.00  sim_tautology_del:                      15
% 3.20/1.00  sim_eq_tautology_del:                   33
% 3.20/1.00  sim_eq_res_simp:                        0
% 3.20/1.00  sim_fw_demodulated:                     81
% 3.20/1.00  sim_bw_demodulated:                     22
% 3.20/1.00  sim_light_normalised:                   44
% 3.20/1.00  sim_joinable_taut:                      0
% 3.20/1.00  sim_joinable_simp:                      0
% 3.20/1.00  sim_ac_normalised:                      0
% 3.20/1.00  sim_smt_subsumption:                    0
% 3.20/1.00  
%------------------------------------------------------------------------------
