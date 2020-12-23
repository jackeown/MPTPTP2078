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
% DateTime   : Thu Dec  3 11:40:06 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  181 (1306 expanded)
%              Number of clauses        :  104 ( 415 expanded)
%              Number of leaves         :   21 ( 273 expanded)
%              Depth                    :   27
%              Number of atoms          :  522 (4575 expanded)
%              Number of equality atoms :  218 (1407 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK3) != sK4
        | ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) )
      & ( k2_subset_1(sK3) = sK4
        | r1_tarski(k3_subset_1(sK3,sK4),sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( k2_subset_1(sK3) != sK4
      | ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) )
    & ( k2_subset_1(sK3) = sK4
      | r1_tarski(k3_subset_1(sK3,sK4),sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f39])).

fof(f70,plain,
    ( k2_subset_1(sK3) = sK4
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f67,f62])).

fof(f82,plain,
    ( k3_subset_1(sK3,k1_xboole_0) = sK4
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(definition_unfolding,[],[f70,f72])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f63,f72])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f53])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

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
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f71,plain,
    ( k2_subset_1(sK3) != sK4
    | ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,
    ( k3_subset_1(sK3,k1_xboole_0) != sK4
    | ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | k3_subset_1(sK3,k1_xboole_0) = sK4 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1182,plain,
    ( k3_subset_1(sK3,k1_xboole_0) = sK4
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1207,plain,
    ( sK4 = sK3
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1182,c_20])).

cnf(c_18,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_371,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_372,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_22,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_382,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_372,c_22])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_553,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_554,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_553])).

cnf(c_607,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_382,c_554])).

cnf(c_1178,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_1497,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK3,sK4))) = k3_subset_1(sK4,k3_subset_1(sK3,sK4))
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1207,c_1178])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1197,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1190,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2097,plain,
    ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_1190])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1198,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7600,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_1198])).

cnf(c_7830,plain,
    ( sK4 = sK3
    | r1_tarski(k3_subset_1(sK4,k3_subset_1(sK3,sK4)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_7600])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_67,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_66,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_68,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_71,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_685,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1584,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_687,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1945,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,sK4)
    | sK4 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_1946,plain,
    ( sK4 != X0
    | sK3 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1945])).

cnf(c_1948,plain,
    ( sK4 != sK4
    | sK3 != sK4
    | r1_tarski(sK4,sK4) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_686,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1586,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_3772,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_3773,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3772])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_411,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_412,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_418,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_412,c_22])).

cnf(c_1180,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1184,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1576,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1184])).

cnf(c_1189,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2713,plain,
    ( sK4 = sK3
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_1189])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | k3_subset_1(sK3,k1_xboole_0) != sK4 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1183,plain,
    ( k3_subset_1(sK3,k1_xboole_0) != sK4
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1241,plain,
    ( sK4 != sK3
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1183,c_20])).

cnf(c_1556,plain,
    ( ~ r2_hidden(sK0(k3_subset_1(sK3,sK4),sK4),sK4)
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1560,plain,
    ( r2_hidden(sK0(k3_subset_1(sK3,sK4),sK4),sK4) != iProver_top
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1556])).

cnf(c_451,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_452,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_1368,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
    inference(equality_resolution,[status(thm)],[c_452])).

cnf(c_2099,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_1190])).

cnf(c_2139,plain,
    ( r2_hidden(sK0(k3_subset_1(sK3,sK4),X0),sK3) = iProver_top
    | r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_2099])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1196,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3193,plain,
    ( r2_hidden(sK0(k3_subset_1(sK3,sK4),X0),X1) = iProver_top
    | r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK3,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_1196])).

cnf(c_3247,plain,
    ( r2_hidden(sK0(k3_subset_1(sK3,sK4),sK4),sK4) = iProver_top
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3193])).

cnf(c_4088,plain,
    ( r1_tarski(sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2713,c_1241,c_1560,c_3247])).

cnf(c_8046,plain,
    ( r1_tarski(k3_subset_1(sK4,k3_subset_1(sK3,sK4)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7830,c_67,c_68,c_71,c_1241,c_1560,c_1584,c_1948,c_2713,c_3247,c_3773])).

cnf(c_8051,plain,
    ( k3_subset_1(sK4,k3_subset_1(sK3,sK4)) = sK4
    | r1_tarski(sK4,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8046,c_1189])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1192,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4712,plain,
    ( sK4 = sK3
    | r2_hidden(X0,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) = iProver_top
    | r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_1192])).

cnf(c_2272,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_1198])).

cnf(c_2285,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k3_subset_1(sK3,sK4))) = k3_subset_1(sK3,k3_subset_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_2272,c_1178])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_442,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_443,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,sK4)) = sK4
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_1365,plain,
    ( k3_subset_1(sK3,k3_subset_1(sK3,sK4)) = sK4 ),
    inference(equality_resolution,[status(thm)],[c_443])).

cnf(c_2287,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k3_subset_1(sK3,sK4))) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_2285,c_1365])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1191,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3144,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2287,c_1191])).

cnf(c_5659,plain,
    ( r2_hidden(X0,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4712,c_67,c_68,c_71,c_1241,c_1560,c_1584,c_1948,c_2713,c_3144,c_3247,c_3773])).

cnf(c_5667,plain,
    ( r2_hidden(sK0(X0,k3_subset_1(sK4,k3_subset_1(sK3,sK4))),sK4) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5659,c_1198])).

cnf(c_6072,plain,
    ( r1_tarski(sK4,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_5667])).

cnf(c_6247,plain,
    ( k3_subset_1(sK4,k3_subset_1(sK3,sK4)) = sK4
    | r1_tarski(k3_subset_1(sK4,k3_subset_1(sK3,sK4)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6072,c_1189])).

cnf(c_8621,plain,
    ( k3_subset_1(sK4,k3_subset_1(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8051,c_67,c_68,c_71,c_1241,c_1560,c_1584,c_1948,c_2713,c_3247,c_3773,c_6247,c_7830])).

cnf(c_354,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k3_subset_1(X3,k3_subset_1(X3,X2)) = X2
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_355,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_365,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_355,c_22])).

cnf(c_606,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_365,c_554])).

cnf(c_1179,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_2012,plain,
    ( k3_subset_1(sK4,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) = k3_subset_1(sK3,sK4)
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1207,c_1179])).

cnf(c_8637,plain,
    ( k3_subset_1(sK4,sK4) = k3_subset_1(sK3,sK4)
    | sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_8621,c_2012])).

cnf(c_24,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_424,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_24])).

cnf(c_425,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_1232,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_425,c_20])).

cnf(c_1571,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_1232])).

cnf(c_8645,plain,
    ( k3_subset_1(sK3,sK4) = k1_xboole_0
    | sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_8637,c_1571])).

cnf(c_10036,plain,
    ( k3_subset_1(sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8645,c_67,c_68,c_71,c_1241,c_1560,c_1584,c_1948,c_2713,c_3247,c_3773])).

cnf(c_10068,plain,
    ( k3_subset_1(sK3,k1_xboole_0) = sK4 ),
    inference(demodulation,[status(thm)],[c_10036,c_1365])).

cnf(c_10070,plain,
    ( sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_10068,c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10070,c_4088,c_3773,c_1948,c_1584,c_71,c_68,c_67])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:06 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 3.06/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.07  
% 3.06/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/1.07  
% 3.06/1.07  ------  iProver source info
% 3.06/1.07  
% 3.06/1.07  git: date: 2020-06-30 10:37:57 +0100
% 3.06/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/1.07  git: non_committed_changes: false
% 3.06/1.07  git: last_make_outside_of_git: false
% 3.06/1.07  
% 3.06/1.07  ------ 
% 3.06/1.07  
% 3.06/1.07  ------ Input Options
% 3.06/1.07  
% 3.06/1.07  --out_options                           all
% 3.06/1.07  --tptp_safe_out                         true
% 3.06/1.07  --problem_path                          ""
% 3.06/1.07  --include_path                          ""
% 3.06/1.07  --clausifier                            res/vclausify_rel
% 3.06/1.07  --clausifier_options                    --mode clausify
% 3.06/1.07  --stdin                                 false
% 3.06/1.07  --stats_out                             all
% 3.06/1.07  
% 3.06/1.07  ------ General Options
% 3.06/1.07  
% 3.06/1.07  --fof                                   false
% 3.06/1.07  --time_out_real                         305.
% 3.06/1.07  --time_out_virtual                      -1.
% 3.06/1.07  --symbol_type_check                     false
% 3.06/1.07  --clausify_out                          false
% 3.06/1.07  --sig_cnt_out                           false
% 3.06/1.07  --trig_cnt_out                          false
% 3.06/1.07  --trig_cnt_out_tolerance                1.
% 3.06/1.07  --trig_cnt_out_sk_spl                   false
% 3.06/1.07  --abstr_cl_out                          false
% 3.06/1.07  
% 3.06/1.07  ------ Global Options
% 3.06/1.07  
% 3.06/1.07  --schedule                              default
% 3.06/1.07  --add_important_lit                     false
% 3.06/1.07  --prop_solver_per_cl                    1000
% 3.06/1.07  --min_unsat_core                        false
% 3.06/1.07  --soft_assumptions                      false
% 3.06/1.07  --soft_lemma_size                       3
% 3.06/1.07  --prop_impl_unit_size                   0
% 3.06/1.07  --prop_impl_unit                        []
% 3.06/1.07  --share_sel_clauses                     true
% 3.06/1.07  --reset_solvers                         false
% 3.06/1.07  --bc_imp_inh                            [conj_cone]
% 3.06/1.07  --conj_cone_tolerance                   3.
% 3.06/1.07  --extra_neg_conj                        none
% 3.06/1.07  --large_theory_mode                     true
% 3.06/1.07  --prolific_symb_bound                   200
% 3.06/1.07  --lt_threshold                          2000
% 3.06/1.07  --clause_weak_htbl                      true
% 3.06/1.07  --gc_record_bc_elim                     false
% 3.06/1.07  
% 3.06/1.07  ------ Preprocessing Options
% 3.06/1.07  
% 3.06/1.07  --preprocessing_flag                    true
% 3.06/1.07  --time_out_prep_mult                    0.1
% 3.06/1.07  --splitting_mode                        input
% 3.06/1.07  --splitting_grd                         true
% 3.06/1.07  --splitting_cvd                         false
% 3.06/1.07  --splitting_cvd_svl                     false
% 3.06/1.07  --splitting_nvd                         32
% 3.06/1.07  --sub_typing                            true
% 3.06/1.07  --prep_gs_sim                           true
% 3.06/1.07  --prep_unflatten                        true
% 3.06/1.07  --prep_res_sim                          true
% 3.06/1.07  --prep_upred                            true
% 3.06/1.07  --prep_sem_filter                       exhaustive
% 3.06/1.07  --prep_sem_filter_out                   false
% 3.06/1.07  --pred_elim                             true
% 3.06/1.07  --res_sim_input                         true
% 3.06/1.07  --eq_ax_congr_red                       true
% 3.06/1.07  --pure_diseq_elim                       true
% 3.06/1.07  --brand_transform                       false
% 3.06/1.07  --non_eq_to_eq                          false
% 3.06/1.07  --prep_def_merge                        true
% 3.06/1.07  --prep_def_merge_prop_impl              false
% 3.06/1.07  --prep_def_merge_mbd                    true
% 3.06/1.07  --prep_def_merge_tr_red                 false
% 3.06/1.07  --prep_def_merge_tr_cl                  false
% 3.06/1.07  --smt_preprocessing                     true
% 3.06/1.07  --smt_ac_axioms                         fast
% 3.06/1.07  --preprocessed_out                      false
% 3.06/1.07  --preprocessed_stats                    false
% 3.06/1.07  
% 3.06/1.07  ------ Abstraction refinement Options
% 3.06/1.07  
% 3.06/1.07  --abstr_ref                             []
% 3.06/1.07  --abstr_ref_prep                        false
% 3.06/1.07  --abstr_ref_until_sat                   false
% 3.06/1.07  --abstr_ref_sig_restrict                funpre
% 3.06/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.07  --abstr_ref_under                       []
% 3.06/1.07  
% 3.06/1.07  ------ SAT Options
% 3.06/1.07  
% 3.06/1.07  --sat_mode                              false
% 3.06/1.07  --sat_fm_restart_options                ""
% 3.06/1.07  --sat_gr_def                            false
% 3.06/1.07  --sat_epr_types                         true
% 3.06/1.07  --sat_non_cyclic_types                  false
% 3.06/1.07  --sat_finite_models                     false
% 3.06/1.07  --sat_fm_lemmas                         false
% 3.06/1.07  --sat_fm_prep                           false
% 3.06/1.07  --sat_fm_uc_incr                        true
% 3.06/1.07  --sat_out_model                         small
% 3.06/1.07  --sat_out_clauses                       false
% 3.06/1.07  
% 3.06/1.07  ------ QBF Options
% 3.06/1.07  
% 3.06/1.07  --qbf_mode                              false
% 3.06/1.07  --qbf_elim_univ                         false
% 3.06/1.07  --qbf_dom_inst                          none
% 3.06/1.07  --qbf_dom_pre_inst                      false
% 3.06/1.07  --qbf_sk_in                             false
% 3.06/1.07  --qbf_pred_elim                         true
% 3.06/1.07  --qbf_split                             512
% 3.06/1.07  
% 3.06/1.07  ------ BMC1 Options
% 3.06/1.07  
% 3.06/1.07  --bmc1_incremental                      false
% 3.06/1.07  --bmc1_axioms                           reachable_all
% 3.06/1.07  --bmc1_min_bound                        0
% 3.06/1.07  --bmc1_max_bound                        -1
% 3.06/1.07  --bmc1_max_bound_default                -1
% 3.06/1.07  --bmc1_symbol_reachability              true
% 3.06/1.07  --bmc1_property_lemmas                  false
% 3.06/1.07  --bmc1_k_induction                      false
% 3.06/1.07  --bmc1_non_equiv_states                 false
% 3.06/1.07  --bmc1_deadlock                         false
% 3.06/1.07  --bmc1_ucm                              false
% 3.06/1.07  --bmc1_add_unsat_core                   none
% 3.06/1.07  --bmc1_unsat_core_children              false
% 3.06/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.07  --bmc1_out_stat                         full
% 3.06/1.07  --bmc1_ground_init                      false
% 3.06/1.07  --bmc1_pre_inst_next_state              false
% 3.06/1.07  --bmc1_pre_inst_state                   false
% 3.06/1.07  --bmc1_pre_inst_reach_state             false
% 3.06/1.07  --bmc1_out_unsat_core                   false
% 3.06/1.07  --bmc1_aig_witness_out                  false
% 3.06/1.07  --bmc1_verbose                          false
% 3.06/1.07  --bmc1_dump_clauses_tptp                false
% 3.06/1.07  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.07  --bmc1_dump_file                        -
% 3.06/1.07  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.07  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.07  --bmc1_ucm_extend_mode                  1
% 3.06/1.07  --bmc1_ucm_init_mode                    2
% 3.06/1.07  --bmc1_ucm_cone_mode                    none
% 3.06/1.07  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.07  --bmc1_ucm_relax_model                  4
% 3.06/1.07  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.07  --bmc1_ucm_layered_model                none
% 3.06/1.07  --bmc1_ucm_max_lemma_size               10
% 3.06/1.07  
% 3.06/1.07  ------ AIG Options
% 3.06/1.07  
% 3.06/1.07  --aig_mode                              false
% 3.06/1.07  
% 3.06/1.07  ------ Instantiation Options
% 3.06/1.07  
% 3.06/1.07  --instantiation_flag                    true
% 3.06/1.07  --inst_sos_flag                         false
% 3.06/1.07  --inst_sos_phase                        true
% 3.06/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.07  --inst_lit_sel_side                     num_symb
% 3.06/1.07  --inst_solver_per_active                1400
% 3.06/1.07  --inst_solver_calls_frac                1.
% 3.06/1.07  --inst_passive_queue_type               priority_queues
% 3.06/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.07  --inst_passive_queues_freq              [25;2]
% 3.06/1.07  --inst_dismatching                      true
% 3.06/1.07  --inst_eager_unprocessed_to_passive     true
% 3.06/1.07  --inst_prop_sim_given                   true
% 3.06/1.07  --inst_prop_sim_new                     false
% 3.06/1.07  --inst_subs_new                         false
% 3.06/1.07  --inst_eq_res_simp                      false
% 3.06/1.07  --inst_subs_given                       false
% 3.06/1.07  --inst_orphan_elimination               true
% 3.06/1.07  --inst_learning_loop_flag               true
% 3.06/1.07  --inst_learning_start                   3000
% 3.06/1.07  --inst_learning_factor                  2
% 3.06/1.07  --inst_start_prop_sim_after_learn       3
% 3.06/1.07  --inst_sel_renew                        solver
% 3.06/1.07  --inst_lit_activity_flag                true
% 3.06/1.07  --inst_restr_to_given                   false
% 3.06/1.07  --inst_activity_threshold               500
% 3.06/1.07  --inst_out_proof                        true
% 3.06/1.07  
% 3.06/1.07  ------ Resolution Options
% 3.06/1.07  
% 3.06/1.07  --resolution_flag                       true
% 3.06/1.07  --res_lit_sel                           adaptive
% 3.06/1.07  --res_lit_sel_side                      none
% 3.06/1.07  --res_ordering                          kbo
% 3.06/1.07  --res_to_prop_solver                    active
% 3.06/1.07  --res_prop_simpl_new                    false
% 3.06/1.07  --res_prop_simpl_given                  true
% 3.06/1.07  --res_passive_queue_type                priority_queues
% 3.06/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.07  --res_passive_queues_freq               [15;5]
% 3.06/1.07  --res_forward_subs                      full
% 3.06/1.07  --res_backward_subs                     full
% 3.06/1.07  --res_forward_subs_resolution           true
% 3.06/1.07  --res_backward_subs_resolution          true
% 3.06/1.07  --res_orphan_elimination                true
% 3.06/1.07  --res_time_limit                        2.
% 3.06/1.07  --res_out_proof                         true
% 3.06/1.07  
% 3.06/1.07  ------ Superposition Options
% 3.06/1.07  
% 3.06/1.07  --superposition_flag                    true
% 3.06/1.07  --sup_passive_queue_type                priority_queues
% 3.06/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.07  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.07  --demod_completeness_check              fast
% 3.06/1.07  --demod_use_ground                      true
% 3.06/1.07  --sup_to_prop_solver                    passive
% 3.06/1.07  --sup_prop_simpl_new                    true
% 3.06/1.07  --sup_prop_simpl_given                  true
% 3.06/1.07  --sup_fun_splitting                     false
% 3.06/1.07  --sup_smt_interval                      50000
% 3.06/1.07  
% 3.06/1.07  ------ Superposition Simplification Setup
% 3.06/1.07  
% 3.06/1.07  --sup_indices_passive                   []
% 3.06/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.07  --sup_full_bw                           [BwDemod]
% 3.06/1.07  --sup_immed_triv                        [TrivRules]
% 3.06/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.07  --sup_immed_bw_main                     []
% 3.06/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.07  
% 3.06/1.07  ------ Combination Options
% 3.06/1.07  
% 3.06/1.07  --comb_res_mult                         3
% 3.06/1.07  --comb_sup_mult                         2
% 3.06/1.07  --comb_inst_mult                        10
% 3.06/1.07  
% 3.06/1.07  ------ Debug Options
% 3.06/1.07  
% 3.06/1.07  --dbg_backtrace                         false
% 3.06/1.07  --dbg_dump_prop_clauses                 false
% 3.06/1.07  --dbg_dump_prop_clauses_file            -
% 3.06/1.07  --dbg_out_stat                          false
% 3.06/1.07  ------ Parsing...
% 3.06/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/1.07  
% 3.06/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.06/1.07  
% 3.06/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/1.07  
% 3.06/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/1.07  ------ Proving...
% 3.06/1.07  ------ Problem Properties 
% 3.06/1.07  
% 3.06/1.07  
% 3.06/1.07  clauses                                 26
% 3.06/1.07  conjectures                             2
% 3.06/1.07  EPR                                     3
% 3.06/1.07  Horn                                    19
% 3.06/1.07  unary                                   4
% 3.06/1.07  binary                                  14
% 3.06/1.07  lits                                    57
% 3.06/1.07  lits eq                                 19
% 3.06/1.07  fd_pure                                 0
% 3.06/1.07  fd_pseudo                               0
% 3.06/1.07  fd_cond                                 0
% 3.06/1.07  fd_pseudo_cond                          6
% 3.06/1.07  AC symbols                              0
% 3.06/1.07  
% 3.06/1.07  ------ Schedule dynamic 5 is on 
% 3.06/1.07  
% 3.06/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/1.07  
% 3.06/1.07  
% 3.06/1.07  ------ 
% 3.06/1.07  Current options:
% 3.06/1.07  ------ 
% 3.06/1.07  
% 3.06/1.07  ------ Input Options
% 3.06/1.07  
% 3.06/1.07  --out_options                           all
% 3.06/1.07  --tptp_safe_out                         true
% 3.06/1.07  --problem_path                          ""
% 3.06/1.07  --include_path                          ""
% 3.06/1.07  --clausifier                            res/vclausify_rel
% 3.06/1.07  --clausifier_options                    --mode clausify
% 3.06/1.07  --stdin                                 false
% 3.06/1.07  --stats_out                             all
% 3.06/1.07  
% 3.06/1.07  ------ General Options
% 3.06/1.07  
% 3.06/1.07  --fof                                   false
% 3.06/1.07  --time_out_real                         305.
% 3.06/1.07  --time_out_virtual                      -1.
% 3.06/1.07  --symbol_type_check                     false
% 3.06/1.07  --clausify_out                          false
% 3.06/1.07  --sig_cnt_out                           false
% 3.06/1.07  --trig_cnt_out                          false
% 3.06/1.07  --trig_cnt_out_tolerance                1.
% 3.06/1.07  --trig_cnt_out_sk_spl                   false
% 3.06/1.07  --abstr_cl_out                          false
% 3.06/1.07  
% 3.06/1.07  ------ Global Options
% 3.06/1.07  
% 3.06/1.07  --schedule                              default
% 3.06/1.07  --add_important_lit                     false
% 3.06/1.07  --prop_solver_per_cl                    1000
% 3.06/1.07  --min_unsat_core                        false
% 3.06/1.07  --soft_assumptions                      false
% 3.06/1.07  --soft_lemma_size                       3
% 3.06/1.07  --prop_impl_unit_size                   0
% 3.06/1.07  --prop_impl_unit                        []
% 3.06/1.07  --share_sel_clauses                     true
% 3.06/1.07  --reset_solvers                         false
% 3.06/1.07  --bc_imp_inh                            [conj_cone]
% 3.06/1.07  --conj_cone_tolerance                   3.
% 3.06/1.07  --extra_neg_conj                        none
% 3.06/1.07  --large_theory_mode                     true
% 3.06/1.07  --prolific_symb_bound                   200
% 3.06/1.07  --lt_threshold                          2000
% 3.06/1.07  --clause_weak_htbl                      true
% 3.06/1.07  --gc_record_bc_elim                     false
% 3.06/1.07  
% 3.06/1.07  ------ Preprocessing Options
% 3.06/1.07  
% 3.06/1.07  --preprocessing_flag                    true
% 3.06/1.07  --time_out_prep_mult                    0.1
% 3.06/1.07  --splitting_mode                        input
% 3.06/1.07  --splitting_grd                         true
% 3.06/1.07  --splitting_cvd                         false
% 3.06/1.07  --splitting_cvd_svl                     false
% 3.06/1.07  --splitting_nvd                         32
% 3.06/1.07  --sub_typing                            true
% 3.06/1.07  --prep_gs_sim                           true
% 3.06/1.07  --prep_unflatten                        true
% 3.06/1.07  --prep_res_sim                          true
% 3.06/1.07  --prep_upred                            true
% 3.06/1.07  --prep_sem_filter                       exhaustive
% 3.06/1.07  --prep_sem_filter_out                   false
% 3.06/1.07  --pred_elim                             true
% 3.06/1.07  --res_sim_input                         true
% 3.06/1.07  --eq_ax_congr_red                       true
% 3.06/1.07  --pure_diseq_elim                       true
% 3.06/1.07  --brand_transform                       false
% 3.06/1.07  --non_eq_to_eq                          false
% 3.06/1.07  --prep_def_merge                        true
% 3.06/1.07  --prep_def_merge_prop_impl              false
% 3.06/1.07  --prep_def_merge_mbd                    true
% 3.06/1.07  --prep_def_merge_tr_red                 false
% 3.06/1.07  --prep_def_merge_tr_cl                  false
% 3.06/1.07  --smt_preprocessing                     true
% 3.06/1.07  --smt_ac_axioms                         fast
% 3.06/1.07  --preprocessed_out                      false
% 3.06/1.07  --preprocessed_stats                    false
% 3.06/1.07  
% 3.06/1.07  ------ Abstraction refinement Options
% 3.06/1.07  
% 3.06/1.07  --abstr_ref                             []
% 3.06/1.07  --abstr_ref_prep                        false
% 3.06/1.07  --abstr_ref_until_sat                   false
% 3.06/1.07  --abstr_ref_sig_restrict                funpre
% 3.06/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.07  --abstr_ref_under                       []
% 3.06/1.07  
% 3.06/1.07  ------ SAT Options
% 3.06/1.07  
% 3.06/1.07  --sat_mode                              false
% 3.06/1.07  --sat_fm_restart_options                ""
% 3.06/1.07  --sat_gr_def                            false
% 3.06/1.07  --sat_epr_types                         true
% 3.06/1.07  --sat_non_cyclic_types                  false
% 3.06/1.07  --sat_finite_models                     false
% 3.06/1.07  --sat_fm_lemmas                         false
% 3.06/1.07  --sat_fm_prep                           false
% 3.06/1.07  --sat_fm_uc_incr                        true
% 3.06/1.07  --sat_out_model                         small
% 3.06/1.07  --sat_out_clauses                       false
% 3.06/1.07  
% 3.06/1.07  ------ QBF Options
% 3.06/1.07  
% 3.06/1.07  --qbf_mode                              false
% 3.06/1.07  --qbf_elim_univ                         false
% 3.06/1.07  --qbf_dom_inst                          none
% 3.06/1.07  --qbf_dom_pre_inst                      false
% 3.06/1.07  --qbf_sk_in                             false
% 3.06/1.07  --qbf_pred_elim                         true
% 3.06/1.07  --qbf_split                             512
% 3.06/1.07  
% 3.06/1.07  ------ BMC1 Options
% 3.06/1.07  
% 3.06/1.07  --bmc1_incremental                      false
% 3.06/1.07  --bmc1_axioms                           reachable_all
% 3.06/1.07  --bmc1_min_bound                        0
% 3.06/1.07  --bmc1_max_bound                        -1
% 3.06/1.07  --bmc1_max_bound_default                -1
% 3.06/1.07  --bmc1_symbol_reachability              true
% 3.06/1.07  --bmc1_property_lemmas                  false
% 3.06/1.07  --bmc1_k_induction                      false
% 3.06/1.07  --bmc1_non_equiv_states                 false
% 3.06/1.07  --bmc1_deadlock                         false
% 3.06/1.07  --bmc1_ucm                              false
% 3.06/1.07  --bmc1_add_unsat_core                   none
% 3.06/1.07  --bmc1_unsat_core_children              false
% 3.06/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.07  --bmc1_out_stat                         full
% 3.06/1.07  --bmc1_ground_init                      false
% 3.06/1.07  --bmc1_pre_inst_next_state              false
% 3.06/1.07  --bmc1_pre_inst_state                   false
% 3.06/1.07  --bmc1_pre_inst_reach_state             false
% 3.06/1.07  --bmc1_out_unsat_core                   false
% 3.06/1.07  --bmc1_aig_witness_out                  false
% 3.06/1.07  --bmc1_verbose                          false
% 3.06/1.07  --bmc1_dump_clauses_tptp                false
% 3.06/1.07  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.07  --bmc1_dump_file                        -
% 3.06/1.07  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.07  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.07  --bmc1_ucm_extend_mode                  1
% 3.06/1.07  --bmc1_ucm_init_mode                    2
% 3.06/1.07  --bmc1_ucm_cone_mode                    none
% 3.06/1.07  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.07  --bmc1_ucm_relax_model                  4
% 3.06/1.07  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.07  --bmc1_ucm_layered_model                none
% 3.06/1.07  --bmc1_ucm_max_lemma_size               10
% 3.06/1.07  
% 3.06/1.07  ------ AIG Options
% 3.06/1.07  
% 3.06/1.07  --aig_mode                              false
% 3.06/1.07  
% 3.06/1.07  ------ Instantiation Options
% 3.06/1.07  
% 3.06/1.07  --instantiation_flag                    true
% 3.06/1.07  --inst_sos_flag                         false
% 3.06/1.07  --inst_sos_phase                        true
% 3.06/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.07  --inst_lit_sel_side                     none
% 3.06/1.07  --inst_solver_per_active                1400
% 3.06/1.07  --inst_solver_calls_frac                1.
% 3.06/1.07  --inst_passive_queue_type               priority_queues
% 3.06/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.07  --inst_passive_queues_freq              [25;2]
% 3.06/1.07  --inst_dismatching                      true
% 3.06/1.07  --inst_eager_unprocessed_to_passive     true
% 3.06/1.07  --inst_prop_sim_given                   true
% 3.06/1.07  --inst_prop_sim_new                     false
% 3.06/1.07  --inst_subs_new                         false
% 3.06/1.07  --inst_eq_res_simp                      false
% 3.06/1.07  --inst_subs_given                       false
% 3.06/1.07  --inst_orphan_elimination               true
% 3.06/1.07  --inst_learning_loop_flag               true
% 3.06/1.07  --inst_learning_start                   3000
% 3.06/1.07  --inst_learning_factor                  2
% 3.06/1.07  --inst_start_prop_sim_after_learn       3
% 3.06/1.07  --inst_sel_renew                        solver
% 3.06/1.07  --inst_lit_activity_flag                true
% 3.06/1.07  --inst_restr_to_given                   false
% 3.06/1.07  --inst_activity_threshold               500
% 3.06/1.07  --inst_out_proof                        true
% 3.06/1.07  
% 3.06/1.07  ------ Resolution Options
% 3.06/1.07  
% 3.06/1.07  --resolution_flag                       false
% 3.06/1.07  --res_lit_sel                           adaptive
% 3.06/1.07  --res_lit_sel_side                      none
% 3.06/1.07  --res_ordering                          kbo
% 3.06/1.07  --res_to_prop_solver                    active
% 3.06/1.07  --res_prop_simpl_new                    false
% 3.06/1.07  --res_prop_simpl_given                  true
% 3.06/1.07  --res_passive_queue_type                priority_queues
% 3.06/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.07  --res_passive_queues_freq               [15;5]
% 3.06/1.07  --res_forward_subs                      full
% 3.06/1.07  --res_backward_subs                     full
% 3.06/1.07  --res_forward_subs_resolution           true
% 3.06/1.07  --res_backward_subs_resolution          true
% 3.06/1.07  --res_orphan_elimination                true
% 3.06/1.07  --res_time_limit                        2.
% 3.06/1.07  --res_out_proof                         true
% 3.06/1.07  
% 3.06/1.07  ------ Superposition Options
% 3.06/1.07  
% 3.06/1.07  --superposition_flag                    true
% 3.06/1.07  --sup_passive_queue_type                priority_queues
% 3.06/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.07  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.07  --demod_completeness_check              fast
% 3.06/1.07  --demod_use_ground                      true
% 3.06/1.07  --sup_to_prop_solver                    passive
% 3.06/1.07  --sup_prop_simpl_new                    true
% 3.06/1.07  --sup_prop_simpl_given                  true
% 3.06/1.07  --sup_fun_splitting                     false
% 3.06/1.07  --sup_smt_interval                      50000
% 3.06/1.07  
% 3.06/1.07  ------ Superposition Simplification Setup
% 3.06/1.07  
% 3.06/1.07  --sup_indices_passive                   []
% 3.06/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.07  --sup_full_bw                           [BwDemod]
% 3.06/1.07  --sup_immed_triv                        [TrivRules]
% 3.06/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.07  --sup_immed_bw_main                     []
% 3.06/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.07  
% 3.06/1.07  ------ Combination Options
% 3.06/1.07  
% 3.06/1.07  --comb_res_mult                         3
% 3.06/1.07  --comb_sup_mult                         2
% 3.06/1.07  --comb_inst_mult                        10
% 3.06/1.07  
% 3.06/1.07  ------ Debug Options
% 3.06/1.07  
% 3.06/1.07  --dbg_backtrace                         false
% 3.06/1.07  --dbg_dump_prop_clauses                 false
% 3.06/1.07  --dbg_dump_prop_clauses_file            -
% 3.06/1.07  --dbg_out_stat                          false
% 3.06/1.07  
% 3.06/1.07  
% 3.06/1.07  
% 3.06/1.07  
% 3.06/1.07  ------ Proving...
% 3.06/1.07  
% 3.06/1.07  
% 3.06/1.07  % SZS status Theorem for theBenchmark.p
% 3.06/1.07  
% 3.06/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/1.07  
% 3.06/1.07  fof(f14,conjecture,(
% 3.06/1.07    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f15,negated_conjecture,(
% 3.06/1.07    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.06/1.07    inference(negated_conjecture,[],[f14])).
% 3.06/1.07  
% 3.06/1.07  fof(f20,plain,(
% 3.06/1.07    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/1.07    inference(ennf_transformation,[],[f15])).
% 3.06/1.07  
% 3.06/1.07  fof(f37,plain,(
% 3.06/1.07    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/1.07    inference(nnf_transformation,[],[f20])).
% 3.06/1.07  
% 3.06/1.07  fof(f38,plain,(
% 3.06/1.07    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/1.07    inference(flattening,[],[f37])).
% 3.06/1.07  
% 3.06/1.07  fof(f39,plain,(
% 3.06/1.07    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK3) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)) & (k2_subset_1(sK3) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 3.06/1.07    introduced(choice_axiom,[])).
% 3.06/1.07  
% 3.06/1.07  fof(f40,plain,(
% 3.06/1.07    (k2_subset_1(sK3) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)) & (k2_subset_1(sK3) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 3.06/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f39])).
% 3.06/1.07  
% 3.06/1.07  fof(f70,plain,(
% 3.06/1.07    k2_subset_1(sK3) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)),
% 3.06/1.07    inference(cnf_transformation,[],[f40])).
% 3.06/1.07  
% 3.06/1.07  fof(f12,axiom,(
% 3.06/1.07    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f67,plain,(
% 3.06/1.07    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.06/1.07    inference(cnf_transformation,[],[f12])).
% 3.06/1.07  
% 3.06/1.07  fof(f7,axiom,(
% 3.06/1.07    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f62,plain,(
% 3.06/1.07    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 3.06/1.07    inference(cnf_transformation,[],[f7])).
% 3.06/1.07  
% 3.06/1.07  fof(f72,plain,(
% 3.06/1.07    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.06/1.07    inference(definition_unfolding,[],[f67,f62])).
% 3.06/1.07  
% 3.06/1.07  fof(f82,plain,(
% 3.06/1.07    k3_subset_1(sK3,k1_xboole_0) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)),
% 3.06/1.07    inference(definition_unfolding,[],[f70,f72])).
% 3.06/1.07  
% 3.06/1.07  fof(f8,axiom,(
% 3.06/1.07    ! [X0] : k2_subset_1(X0) = X0),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f63,plain,(
% 3.06/1.07    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.06/1.07    inference(cnf_transformation,[],[f8])).
% 3.06/1.07  
% 3.06/1.07  fof(f79,plain,(
% 3.06/1.07    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.06/1.07    inference(definition_unfolding,[],[f63,f72])).
% 3.06/1.07  
% 3.06/1.07  fof(f6,axiom,(
% 3.06/1.07    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f17,plain,(
% 3.06/1.07    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.06/1.07    inference(ennf_transformation,[],[f6])).
% 3.06/1.07  
% 3.06/1.07  fof(f36,plain,(
% 3.06/1.07    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.06/1.07    inference(nnf_transformation,[],[f17])).
% 3.06/1.07  
% 3.06/1.07  fof(f59,plain,(
% 3.06/1.07    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.06/1.07    inference(cnf_transformation,[],[f36])).
% 3.06/1.07  
% 3.06/1.07  fof(f9,axiom,(
% 3.06/1.07    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f18,plain,(
% 3.06/1.07    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/1.07    inference(ennf_transformation,[],[f9])).
% 3.06/1.07  
% 3.06/1.07  fof(f64,plain,(
% 3.06/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/1.07    inference(cnf_transformation,[],[f18])).
% 3.06/1.07  
% 3.06/1.07  fof(f4,axiom,(
% 3.06/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f53,plain,(
% 3.06/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.06/1.07    inference(cnf_transformation,[],[f4])).
% 3.06/1.07  
% 3.06/1.07  fof(f80,plain,(
% 3.06/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/1.07    inference(definition_unfolding,[],[f64,f53])).
% 3.06/1.07  
% 3.06/1.07  fof(f10,axiom,(
% 3.06/1.07    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f65,plain,(
% 3.06/1.07    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.06/1.07    inference(cnf_transformation,[],[f10])).
% 3.06/1.07  
% 3.06/1.07  fof(f5,axiom,(
% 3.06/1.07    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f32,plain,(
% 3.06/1.07    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.06/1.07    inference(nnf_transformation,[],[f5])).
% 3.06/1.07  
% 3.06/1.07  fof(f33,plain,(
% 3.06/1.07    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.06/1.07    inference(rectify,[],[f32])).
% 3.06/1.07  
% 3.06/1.07  fof(f34,plain,(
% 3.06/1.07    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.06/1.07    introduced(choice_axiom,[])).
% 3.06/1.07  
% 3.06/1.07  fof(f35,plain,(
% 3.06/1.07    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.06/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 3.06/1.07  
% 3.06/1.07  fof(f55,plain,(
% 3.06/1.07    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.06/1.07    inference(cnf_transformation,[],[f35])).
% 3.06/1.07  
% 3.06/1.07  fof(f88,plain,(
% 3.06/1.07    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.06/1.07    inference(equality_resolution,[],[f55])).
% 3.06/1.07  
% 3.06/1.07  fof(f1,axiom,(
% 3.06/1.07    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f16,plain,(
% 3.06/1.07    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.06/1.07    inference(ennf_transformation,[],[f1])).
% 3.06/1.07  
% 3.06/1.07  fof(f21,plain,(
% 3.06/1.07    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.07    inference(nnf_transformation,[],[f16])).
% 3.06/1.07  
% 3.06/1.07  fof(f22,plain,(
% 3.06/1.07    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.07    inference(rectify,[],[f21])).
% 3.06/1.07  
% 3.06/1.07  fof(f23,plain,(
% 3.06/1.07    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.06/1.07    introduced(choice_axiom,[])).
% 3.06/1.07  
% 3.06/1.07  fof(f24,plain,(
% 3.06/1.07    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.06/1.07  
% 3.06/1.07  fof(f42,plain,(
% 3.06/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.06/1.07    inference(cnf_transformation,[],[f24])).
% 3.06/1.07  
% 3.06/1.07  fof(f2,axiom,(
% 3.06/1.07    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f25,plain,(
% 3.06/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.06/1.07    inference(nnf_transformation,[],[f2])).
% 3.06/1.07  
% 3.06/1.07  fof(f26,plain,(
% 3.06/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.06/1.07    inference(flattening,[],[f25])).
% 3.06/1.07  
% 3.06/1.07  fof(f27,plain,(
% 3.06/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.06/1.07    inference(rectify,[],[f26])).
% 3.06/1.07  
% 3.06/1.07  fof(f28,plain,(
% 3.06/1.07    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.06/1.07    introduced(choice_axiom,[])).
% 3.06/1.07  
% 3.06/1.07  fof(f29,plain,(
% 3.06/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.06/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 3.06/1.07  
% 3.06/1.07  fof(f44,plain,(
% 3.06/1.07    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.06/1.07    inference(cnf_transformation,[],[f29])).
% 3.06/1.07  
% 3.06/1.07  fof(f78,plain,(
% 3.06/1.07    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.06/1.07    inference(definition_unfolding,[],[f44,f53])).
% 3.06/1.07  
% 3.06/1.07  fof(f85,plain,(
% 3.06/1.07    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.06/1.07    inference(equality_resolution,[],[f78])).
% 3.06/1.07  
% 3.06/1.07  fof(f43,plain,(
% 3.06/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.06/1.07    inference(cnf_transformation,[],[f24])).
% 3.06/1.07  
% 3.06/1.07  fof(f3,axiom,(
% 3.06/1.07    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f30,plain,(
% 3.06/1.07    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.06/1.07    inference(nnf_transformation,[],[f3])).
% 3.06/1.07  
% 3.06/1.07  fof(f31,plain,(
% 3.06/1.07    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.06/1.07    inference(flattening,[],[f30])).
% 3.06/1.07  
% 3.06/1.07  fof(f50,plain,(
% 3.06/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.06/1.07    inference(cnf_transformation,[],[f31])).
% 3.06/1.07  
% 3.06/1.07  fof(f87,plain,(
% 3.06/1.07    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.06/1.07    inference(equality_resolution,[],[f50])).
% 3.06/1.07  
% 3.06/1.07  fof(f52,plain,(
% 3.06/1.07    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.06/1.07    inference(cnf_transformation,[],[f31])).
% 3.06/1.07  
% 3.06/1.07  fof(f58,plain,(
% 3.06/1.07    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.06/1.07    inference(cnf_transformation,[],[f36])).
% 3.06/1.07  
% 3.06/1.07  fof(f69,plain,(
% 3.06/1.07    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 3.06/1.07    inference(cnf_transformation,[],[f40])).
% 3.06/1.07  
% 3.06/1.07  fof(f54,plain,(
% 3.06/1.07    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.06/1.07    inference(cnf_transformation,[],[f35])).
% 3.06/1.07  
% 3.06/1.07  fof(f89,plain,(
% 3.06/1.07    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.06/1.07    inference(equality_resolution,[],[f54])).
% 3.06/1.07  
% 3.06/1.07  fof(f71,plain,(
% 3.06/1.07    k2_subset_1(sK3) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)),
% 3.06/1.07    inference(cnf_transformation,[],[f40])).
% 3.06/1.07  
% 3.06/1.07  fof(f81,plain,(
% 3.06/1.07    k3_subset_1(sK3,k1_xboole_0) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)),
% 3.06/1.07    inference(definition_unfolding,[],[f71,f72])).
% 3.06/1.07  
% 3.06/1.07  fof(f41,plain,(
% 3.06/1.07    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.06/1.07    inference(cnf_transformation,[],[f24])).
% 3.06/1.07  
% 3.06/1.07  fof(f46,plain,(
% 3.06/1.07    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.06/1.07    inference(cnf_transformation,[],[f29])).
% 3.06/1.07  
% 3.06/1.07  fof(f76,plain,(
% 3.06/1.07    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.06/1.07    inference(definition_unfolding,[],[f46,f53])).
% 3.06/1.07  
% 3.06/1.07  fof(f83,plain,(
% 3.06/1.07    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.06/1.07    inference(equality_resolution,[],[f76])).
% 3.06/1.07  
% 3.06/1.07  fof(f11,axiom,(
% 3.06/1.07    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f19,plain,(
% 3.06/1.07    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/1.07    inference(ennf_transformation,[],[f11])).
% 3.06/1.07  
% 3.06/1.07  fof(f66,plain,(
% 3.06/1.07    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/1.07    inference(cnf_transformation,[],[f19])).
% 3.06/1.07  
% 3.06/1.07  fof(f45,plain,(
% 3.06/1.07    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.06/1.07    inference(cnf_transformation,[],[f29])).
% 3.06/1.07  
% 3.06/1.07  fof(f77,plain,(
% 3.06/1.07    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.06/1.07    inference(definition_unfolding,[],[f45,f53])).
% 3.06/1.07  
% 3.06/1.07  fof(f84,plain,(
% 3.06/1.07    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.06/1.07    inference(equality_resolution,[],[f77])).
% 3.06/1.07  
% 3.06/1.07  fof(f13,axiom,(
% 3.06/1.07    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.06/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.07  
% 3.06/1.07  fof(f68,plain,(
% 3.06/1.07    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.06/1.07    inference(cnf_transformation,[],[f13])).
% 3.06/1.07  
% 3.06/1.07  cnf(c_26,negated_conjecture,
% 3.06/1.07      ( r1_tarski(k3_subset_1(sK3,sK4),sK4)
% 3.06/1.07      | k3_subset_1(sK3,k1_xboole_0) = sK4 ),
% 3.06/1.07      inference(cnf_transformation,[],[f82]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1182,plain,
% 3.06/1.07      ( k3_subset_1(sK3,k1_xboole_0) = sK4
% 3.06/1.07      | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_20,plain,
% 3.06/1.07      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.06/1.07      inference(cnf_transformation,[],[f79]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1207,plain,
% 3.06/1.07      ( sK4 = sK3 | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
% 3.06/1.07      inference(demodulation,[status(thm)],[c_1182,c_20]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_18,plain,
% 3.06/1.07      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.06/1.07      inference(cnf_transformation,[],[f59]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_21,plain,
% 3.06/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/1.07      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.06/1.07      inference(cnf_transformation,[],[f80]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_371,plain,
% 3.06/1.07      ( ~ r2_hidden(X0,X1)
% 3.06/1.07      | v1_xboole_0(X1)
% 3.06/1.07      | X2 != X0
% 3.06/1.07      | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
% 3.06/1.07      | k1_zfmisc_1(X3) != X1 ),
% 3.06/1.07      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_372,plain,
% 3.06/1.07      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.06/1.07      | v1_xboole_0(k1_zfmisc_1(X1))
% 3.06/1.07      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.06/1.07      inference(unflattening,[status(thm)],[c_371]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_22,plain,
% 3.06/1.07      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.06/1.07      inference(cnf_transformation,[],[f65]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_382,plain,
% 3.06/1.07      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.06/1.07      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.06/1.07      inference(forward_subsumption_resolution,
% 3.06/1.07                [status(thm)],
% 3.06/1.07                [c_372,c_22]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_14,plain,
% 3.06/1.07      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.06/1.07      inference(cnf_transformation,[],[f88]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_553,plain,
% 3.06/1.07      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.06/1.07      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_554,plain,
% 3.06/1.07      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.06/1.07      inference(renaming,[status(thm)],[c_553]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_607,plain,
% 3.06/1.07      ( ~ r1_tarski(X0,X1)
% 3.06/1.07      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.06/1.07      inference(bin_hyper_res,[status(thm)],[c_382,c_554]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1178,plain,
% 3.06/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.06/1.07      | r1_tarski(X1,X0) != iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1497,plain,
% 3.06/1.07      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK3,sK4))) = k3_subset_1(sK4,k3_subset_1(sK3,sK4))
% 3.06/1.07      | sK4 = sK3 ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_1207,c_1178]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1,plain,
% 3.06/1.07      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.06/1.07      inference(cnf_transformation,[],[f42]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1197,plain,
% 3.06/1.07      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.06/1.07      | r1_tarski(X0,X1) = iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_8,plain,
% 3.06/1.07      ( r2_hidden(X0,X1)
% 3.06/1.07      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.06/1.07      inference(cnf_transformation,[],[f85]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1190,plain,
% 3.06/1.07      ( r2_hidden(X0,X1) = iProver_top
% 3.06/1.07      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_2097,plain,
% 3.06/1.07      ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
% 3.06/1.07      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_1197,c_1190]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_0,plain,
% 3.06/1.07      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.06/1.07      inference(cnf_transformation,[],[f43]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1198,plain,
% 3.06/1.07      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.06/1.07      | r1_tarski(X0,X1) = iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_7600,plain,
% 3.06/1.07      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_2097,c_1198]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_7830,plain,
% 3.06/1.07      ( sK4 = sK3
% 3.06/1.07      | r1_tarski(k3_subset_1(sK4,k3_subset_1(sK3,sK4)),sK4) = iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_1497,c_7600]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_11,plain,
% 3.06/1.07      ( r1_tarski(X0,X0) ),
% 3.06/1.07      inference(cnf_transformation,[],[f87]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_67,plain,
% 3.06/1.07      ( r1_tarski(sK4,sK4) ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_11]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_66,plain,
% 3.06/1.07      ( r1_tarski(X0,X0) = iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_68,plain,
% 3.06/1.07      ( r1_tarski(sK4,sK4) = iProver_top ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_66]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_9,plain,
% 3.06/1.07      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.06/1.07      inference(cnf_transformation,[],[f52]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_71,plain,
% 3.06/1.07      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_9]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_685,plain,( X0 = X0 ),theory(equality) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1584,plain,
% 3.06/1.07      ( sK3 = sK3 ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_685]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_687,plain,
% 3.06/1.07      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.06/1.07      theory(equality) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1945,plain,
% 3.06/1.07      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,sK4) | sK4 != X1 | sK3 != X0 ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_687]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1946,plain,
% 3.06/1.07      ( sK4 != X0
% 3.06/1.07      | sK3 != X1
% 3.06/1.07      | r1_tarski(X1,X0) != iProver_top
% 3.06/1.07      | r1_tarski(sK3,sK4) = iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_1945]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1948,plain,
% 3.06/1.07      ( sK4 != sK4
% 3.06/1.07      | sK3 != sK4
% 3.06/1.07      | r1_tarski(sK4,sK4) != iProver_top
% 3.06/1.07      | r1_tarski(sK3,sK4) = iProver_top ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_1946]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_686,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1586,plain,
% 3.06/1.07      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_686]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_3772,plain,
% 3.06/1.07      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_1586]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_3773,plain,
% 3.06/1.07      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_3772]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_19,plain,
% 3.06/1.07      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.06/1.07      inference(cnf_transformation,[],[f58]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_27,negated_conjecture,
% 3.06/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 3.06/1.07      inference(cnf_transformation,[],[f69]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_411,plain,
% 3.06/1.07      ( r2_hidden(X0,X1)
% 3.06/1.07      | v1_xboole_0(X1)
% 3.06/1.07      | k1_zfmisc_1(sK3) != X1
% 3.06/1.07      | sK4 != X0 ),
% 3.06/1.07      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_412,plain,
% 3.06/1.07      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 3.06/1.07      inference(unflattening,[status(thm)],[c_411]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_418,plain,
% 3.06/1.07      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
% 3.06/1.07      inference(forward_subsumption_resolution,
% 3.06/1.07                [status(thm)],
% 3.06/1.07                [c_412,c_22]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1180,plain,
% 3.06/1.07      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_15,plain,
% 3.06/1.07      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.06/1.07      inference(cnf_transformation,[],[f89]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1184,plain,
% 3.06/1.07      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.06/1.07      | r1_tarski(X0,X1) = iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1576,plain,
% 3.06/1.07      ( r1_tarski(sK4,sK3) = iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_1180,c_1184]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1189,plain,
% 3.06/1.07      ( X0 = X1
% 3.06/1.07      | r1_tarski(X1,X0) != iProver_top
% 3.06/1.07      | r1_tarski(X0,X1) != iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_2713,plain,
% 3.06/1.07      ( sK4 = sK3 | r1_tarski(sK3,sK4) != iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_1576,c_1189]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_25,negated_conjecture,
% 3.06/1.07      ( ~ r1_tarski(k3_subset_1(sK3,sK4),sK4)
% 3.06/1.07      | k3_subset_1(sK3,k1_xboole_0) != sK4 ),
% 3.06/1.07      inference(cnf_transformation,[],[f81]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1183,plain,
% 3.06/1.07      ( k3_subset_1(sK3,k1_xboole_0) != sK4
% 3.06/1.07      | r1_tarski(k3_subset_1(sK3,sK4),sK4) != iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1241,plain,
% 3.06/1.07      ( sK4 != sK3 | r1_tarski(k3_subset_1(sK3,sK4),sK4) != iProver_top ),
% 3.06/1.07      inference(demodulation,[status(thm)],[c_1183,c_20]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1556,plain,
% 3.06/1.07      ( ~ r2_hidden(sK0(k3_subset_1(sK3,sK4),sK4),sK4)
% 3.06/1.07      | r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_0]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1560,plain,
% 3.06/1.07      ( r2_hidden(sK0(k3_subset_1(sK3,sK4),sK4),sK4) != iProver_top
% 3.06/1.07      | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_1556]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_451,plain,
% 3.06/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.06/1.07      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 3.06/1.07      | sK4 != X1 ),
% 3.06/1.07      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_452,plain,
% 3.06/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
% 3.06/1.07      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 3.06/1.07      inference(unflattening,[status(thm)],[c_451]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1368,plain,
% 3.06/1.07      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
% 3.06/1.07      inference(equality_resolution,[status(thm)],[c_452]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_2099,plain,
% 3.06/1.07      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
% 3.06/1.07      | r2_hidden(X0,sK3) = iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_1368,c_1190]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_2139,plain,
% 3.06/1.07      ( r2_hidden(sK0(k3_subset_1(sK3,sK4),X0),sK3) = iProver_top
% 3.06/1.07      | r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_1197,c_2099]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_2,plain,
% 3.06/1.07      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.06/1.07      inference(cnf_transformation,[],[f41]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1196,plain,
% 3.06/1.07      ( r2_hidden(X0,X1) != iProver_top
% 3.06/1.07      | r2_hidden(X0,X2) = iProver_top
% 3.06/1.07      | r1_tarski(X1,X2) != iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_3193,plain,
% 3.06/1.07      ( r2_hidden(sK0(k3_subset_1(sK3,sK4),X0),X1) = iProver_top
% 3.06/1.07      | r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top
% 3.06/1.07      | r1_tarski(sK3,X1) != iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_2139,c_1196]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_3247,plain,
% 3.06/1.07      ( r2_hidden(sK0(k3_subset_1(sK3,sK4),sK4),sK4) = iProver_top
% 3.06/1.07      | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top
% 3.06/1.07      | r1_tarski(sK3,sK4) != iProver_top ),
% 3.06/1.07      inference(instantiation,[status(thm)],[c_3193]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_4088,plain,
% 3.06/1.07      ( r1_tarski(sK3,sK4) != iProver_top ),
% 3.06/1.07      inference(global_propositional_subsumption,
% 3.06/1.07                [status(thm)],
% 3.06/1.07                [c_2713,c_1241,c_1560,c_3247]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_8046,plain,
% 3.06/1.07      ( r1_tarski(k3_subset_1(sK4,k3_subset_1(sK3,sK4)),sK4) = iProver_top ),
% 3.06/1.07      inference(global_propositional_subsumption,
% 3.06/1.07                [status(thm)],
% 3.06/1.07                [c_7830,c_67,c_68,c_71,c_1241,c_1560,c_1584,c_1948,
% 3.06/1.07                 c_2713,c_3247,c_3773]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_8051,plain,
% 3.06/1.07      ( k3_subset_1(sK4,k3_subset_1(sK3,sK4)) = sK4
% 3.06/1.07      | r1_tarski(sK4,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) != iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_8046,c_1189]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_6,plain,
% 3.06/1.07      ( ~ r2_hidden(X0,X1)
% 3.06/1.07      | r2_hidden(X0,X2)
% 3.06/1.07      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.06/1.07      inference(cnf_transformation,[],[f83]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1192,plain,
% 3.06/1.07      ( r2_hidden(X0,X1) != iProver_top
% 3.06/1.07      | r2_hidden(X0,X2) = iProver_top
% 3.06/1.07      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_4712,plain,
% 3.06/1.07      ( sK4 = sK3
% 3.06/1.07      | r2_hidden(X0,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) = iProver_top
% 3.06/1.07      | r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
% 3.06/1.07      | r2_hidden(X0,sK4) != iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_1497,c_1192]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_2272,plain,
% 3.06/1.07      ( r1_tarski(k3_subset_1(sK3,sK4),sK3) = iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_2139,c_1198]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_2285,plain,
% 3.06/1.07      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k3_subset_1(sK3,sK4))) = k3_subset_1(sK3,k3_subset_1(sK3,sK4)) ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_2272,c_1178]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_23,plain,
% 3.06/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/1.07      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.06/1.07      inference(cnf_transformation,[],[f66]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_442,plain,
% 3.06/1.07      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.06/1.07      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 3.06/1.07      | sK4 != X1 ),
% 3.06/1.07      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_443,plain,
% 3.06/1.07      ( k3_subset_1(X0,k3_subset_1(X0,sK4)) = sK4
% 3.06/1.07      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 3.06/1.07      inference(unflattening,[status(thm)],[c_442]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1365,plain,
% 3.06/1.07      ( k3_subset_1(sK3,k3_subset_1(sK3,sK4)) = sK4 ),
% 3.06/1.07      inference(equality_resolution,[status(thm)],[c_443]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_2287,plain,
% 3.06/1.07      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k3_subset_1(sK3,sK4))) = sK4 ),
% 3.06/1.07      inference(light_normalisation,[status(thm)],[c_2285,c_1365]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_7,plain,
% 3.06/1.07      ( ~ r2_hidden(X0,X1)
% 3.06/1.07      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.06/1.07      inference(cnf_transformation,[],[f84]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1191,plain,
% 3.06/1.07      ( r2_hidden(X0,X1) != iProver_top
% 3.06/1.07      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_3144,plain,
% 3.06/1.07      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
% 3.06/1.07      | r2_hidden(X0,sK4) != iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_2287,c_1191]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_5659,plain,
% 3.06/1.07      ( r2_hidden(X0,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) = iProver_top
% 3.06/1.07      | r2_hidden(X0,sK4) != iProver_top ),
% 3.06/1.07      inference(global_propositional_subsumption,
% 3.06/1.07                [status(thm)],
% 3.06/1.07                [c_4712,c_67,c_68,c_71,c_1241,c_1560,c_1584,c_1948,
% 3.06/1.07                 c_2713,c_3144,c_3247,c_3773]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_5667,plain,
% 3.06/1.07      ( r2_hidden(sK0(X0,k3_subset_1(sK4,k3_subset_1(sK3,sK4))),sK4) != iProver_top
% 3.06/1.07      | r1_tarski(X0,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) = iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_5659,c_1198]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_6072,plain,
% 3.06/1.07      ( r1_tarski(sK4,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) = iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_1197,c_5667]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_6247,plain,
% 3.06/1.07      ( k3_subset_1(sK4,k3_subset_1(sK3,sK4)) = sK4
% 3.06/1.07      | r1_tarski(k3_subset_1(sK4,k3_subset_1(sK3,sK4)),sK4) != iProver_top ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_6072,c_1189]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_8621,plain,
% 3.06/1.07      ( k3_subset_1(sK4,k3_subset_1(sK3,sK4)) = sK4 ),
% 3.06/1.07      inference(global_propositional_subsumption,
% 3.06/1.07                [status(thm)],
% 3.06/1.07                [c_8051,c_67,c_68,c_71,c_1241,c_1560,c_1584,c_1948,
% 3.06/1.07                 c_2713,c_3247,c_3773,c_6247,c_7830]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_354,plain,
% 3.06/1.07      ( ~ r2_hidden(X0,X1)
% 3.06/1.07      | v1_xboole_0(X1)
% 3.06/1.07      | X2 != X0
% 3.06/1.07      | k3_subset_1(X3,k3_subset_1(X3,X2)) = X2
% 3.06/1.07      | k1_zfmisc_1(X3) != X1 ),
% 3.06/1.07      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_355,plain,
% 3.06/1.07      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.06/1.07      | v1_xboole_0(k1_zfmisc_1(X1))
% 3.06/1.07      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.06/1.07      inference(unflattening,[status(thm)],[c_354]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_365,plain,
% 3.06/1.07      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.06/1.07      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.06/1.07      inference(forward_subsumption_resolution,
% 3.06/1.07                [status(thm)],
% 3.06/1.07                [c_355,c_22]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_606,plain,
% 3.06/1.07      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.06/1.07      inference(bin_hyper_res,[status(thm)],[c_365,c_554]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1179,plain,
% 3.06/1.07      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.06/1.07      | r1_tarski(X1,X0) != iProver_top ),
% 3.06/1.07      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_2012,plain,
% 3.06/1.07      ( k3_subset_1(sK4,k3_subset_1(sK4,k3_subset_1(sK3,sK4))) = k3_subset_1(sK3,sK4)
% 3.06/1.07      | sK4 = sK3 ),
% 3.06/1.07      inference(superposition,[status(thm)],[c_1207,c_1179]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_8637,plain,
% 3.06/1.07      ( k3_subset_1(sK4,sK4) = k3_subset_1(sK3,sK4) | sK4 = sK3 ),
% 3.06/1.07      inference(demodulation,[status(thm)],[c_8621,c_2012]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_24,plain,
% 3.06/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.06/1.07      inference(cnf_transformation,[],[f68]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_424,plain,
% 3.06/1.07      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.06/1.07      | k1_zfmisc_1(X2) != k1_zfmisc_1(X0)
% 3.06/1.07      | k1_xboole_0 != X1 ),
% 3.06/1.07      inference(resolution_lifted,[status(thm)],[c_23,c_24]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_425,plain,
% 3.06/1.07      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.06/1.07      | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
% 3.06/1.07      inference(unflattening,[status(thm)],[c_424]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1232,plain,
% 3.06/1.07      ( k3_subset_1(X0,X0) = k1_xboole_0
% 3.06/1.07      | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
% 3.06/1.07      inference(light_normalisation,[status(thm)],[c_425,c_20]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_1571,plain,
% 3.06/1.07      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.06/1.07      inference(equality_resolution,[status(thm)],[c_1232]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_8645,plain,
% 3.06/1.07      ( k3_subset_1(sK3,sK4) = k1_xboole_0 | sK4 = sK3 ),
% 3.06/1.07      inference(demodulation,[status(thm)],[c_8637,c_1571]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_10036,plain,
% 3.06/1.07      ( k3_subset_1(sK3,sK4) = k1_xboole_0 ),
% 3.06/1.07      inference(global_propositional_subsumption,
% 3.06/1.07                [status(thm)],
% 3.06/1.07                [c_8645,c_67,c_68,c_71,c_1241,c_1560,c_1584,c_1948,
% 3.06/1.07                 c_2713,c_3247,c_3773]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_10068,plain,
% 3.06/1.07      ( k3_subset_1(sK3,k1_xboole_0) = sK4 ),
% 3.06/1.07      inference(demodulation,[status(thm)],[c_10036,c_1365]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(c_10070,plain,
% 3.06/1.07      ( sK4 = sK3 ),
% 3.06/1.07      inference(demodulation,[status(thm)],[c_10068,c_20]) ).
% 3.06/1.07  
% 3.06/1.07  cnf(contradiction,plain,
% 3.06/1.07      ( $false ),
% 3.06/1.07      inference(minisat,
% 3.06/1.07                [status(thm)],
% 3.06/1.07                [c_10070,c_4088,c_3773,c_1948,c_1584,c_71,c_68,c_67]) ).
% 3.06/1.07  
% 3.06/1.07  
% 3.06/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.07  
% 3.06/1.07  ------                               Statistics
% 3.06/1.07  
% 3.06/1.07  ------ General
% 3.06/1.07  
% 3.06/1.07  abstr_ref_over_cycles:                  0
% 3.06/1.07  abstr_ref_under_cycles:                 0
% 3.06/1.07  gc_basic_clause_elim:                   0
% 3.06/1.07  forced_gc_time:                         0
% 3.06/1.07  parsing_time:                           0.014
% 3.06/1.07  unif_index_cands_time:                  0.
% 3.06/1.07  unif_index_add_time:                    0.
% 3.06/1.07  orderings_time:                         0.
% 3.06/1.07  out_proof_time:                         0.011
% 3.06/1.07  total_time:                             0.303
% 3.06/1.07  num_of_symbols:                         45
% 3.06/1.07  num_of_terms:                           12198
% 3.06/1.07  
% 3.06/1.07  ------ Preprocessing
% 3.06/1.07  
% 3.06/1.07  num_of_splits:                          0
% 3.06/1.07  num_of_split_atoms:                     0
% 3.06/1.07  num_of_reused_defs:                     0
% 3.06/1.07  num_eq_ax_congr_red:                    28
% 3.06/1.07  num_of_sem_filtered_clauses:            1
% 3.06/1.07  num_of_subtypes:                        0
% 3.06/1.07  monotx_restored_types:                  0
% 3.06/1.07  sat_num_of_epr_types:                   0
% 3.06/1.07  sat_num_of_non_cyclic_types:            0
% 3.06/1.07  sat_guarded_non_collapsed_types:        0
% 3.06/1.07  num_pure_diseq_elim:                    0
% 3.06/1.07  simp_replaced_by:                       0
% 3.06/1.07  res_preprocessed:                       122
% 3.06/1.07  prep_upred:                             0
% 3.06/1.07  prep_unflattend:                        20
% 3.06/1.07  smt_new_axioms:                         0
% 3.06/1.07  pred_elim_cands:                        2
% 3.06/1.07  pred_elim:                              2
% 3.06/1.07  pred_elim_cl:                           1
% 3.06/1.07  pred_elim_cycles:                       4
% 3.06/1.07  merged_defs:                            16
% 3.06/1.07  merged_defs_ncl:                        0
% 3.06/1.07  bin_hyper_res:                          18
% 3.06/1.07  prep_cycles:                            4
% 3.06/1.07  pred_elim_time:                         0.005
% 3.06/1.07  splitting_time:                         0.
% 3.06/1.07  sem_filter_time:                        0.
% 3.06/1.07  monotx_time:                            0.001
% 3.06/1.07  subtype_inf_time:                       0.
% 3.06/1.07  
% 3.06/1.07  ------ Problem properties
% 3.06/1.07  
% 3.06/1.07  clauses:                                26
% 3.06/1.07  conjectures:                            2
% 3.06/1.07  epr:                                    3
% 3.06/1.07  horn:                                   19
% 3.06/1.07  ground:                                 3
% 3.06/1.07  unary:                                  4
% 3.06/1.07  binary:                                 14
% 3.06/1.07  lits:                                   57
% 3.06/1.07  lits_eq:                                19
% 3.06/1.07  fd_pure:                                0
% 3.06/1.07  fd_pseudo:                              0
% 3.06/1.07  fd_cond:                                0
% 3.06/1.07  fd_pseudo_cond:                         6
% 3.06/1.07  ac_symbols:                             0
% 3.06/1.07  
% 3.06/1.07  ------ Propositional Solver
% 3.06/1.07  
% 3.06/1.07  prop_solver_calls:                      29
% 3.06/1.07  prop_fast_solver_calls:                 790
% 3.06/1.07  smt_solver_calls:                       0
% 3.06/1.07  smt_fast_solver_calls:                  0
% 3.06/1.07  prop_num_of_clauses:                    4179
% 3.06/1.07  prop_preprocess_simplified:             9496
% 3.06/1.07  prop_fo_subsumed:                       13
% 3.06/1.07  prop_solver_time:                       0.
% 3.06/1.07  smt_solver_time:                        0.
% 3.06/1.07  smt_fast_solver_time:                   0.
% 3.06/1.07  prop_fast_solver_time:                  0.
% 3.06/1.07  prop_unsat_core_time:                   0.
% 3.06/1.07  
% 3.06/1.07  ------ QBF
% 3.06/1.07  
% 3.06/1.07  qbf_q_res:                              0
% 3.06/1.07  qbf_num_tautologies:                    0
% 3.06/1.07  qbf_prep_cycles:                        0
% 3.06/1.07  
% 3.06/1.07  ------ BMC1
% 3.06/1.07  
% 3.06/1.07  bmc1_current_bound:                     -1
% 3.06/1.07  bmc1_last_solved_bound:                 -1
% 3.06/1.07  bmc1_unsat_core_size:                   -1
% 3.06/1.07  bmc1_unsat_core_parents_size:           -1
% 3.06/1.07  bmc1_merge_next_fun:                    0
% 3.06/1.07  bmc1_unsat_core_clauses_time:           0.
% 3.06/1.07  
% 3.06/1.07  ------ Instantiation
% 3.06/1.07  
% 3.06/1.07  inst_num_of_clauses:                    1074
% 3.06/1.07  inst_num_in_passive:                    245
% 3.06/1.07  inst_num_in_active:                     363
% 3.06/1.07  inst_num_in_unprocessed:                466
% 3.06/1.07  inst_num_of_loops:                      460
% 3.06/1.07  inst_num_of_learning_restarts:          0
% 3.06/1.07  inst_num_moves_active_passive:          94
% 3.06/1.07  inst_lit_activity:                      0
% 3.06/1.07  inst_lit_activity_moves:                0
% 3.06/1.07  inst_num_tautologies:                   0
% 3.06/1.07  inst_num_prop_implied:                  0
% 3.06/1.07  inst_num_existing_simplified:           0
% 3.06/1.07  inst_num_eq_res_simplified:             0
% 3.06/1.07  inst_num_child_elim:                    0
% 3.06/1.07  inst_num_of_dismatching_blockings:      446
% 3.06/1.07  inst_num_of_non_proper_insts:           837
% 3.06/1.07  inst_num_of_duplicates:                 0
% 3.06/1.07  inst_inst_num_from_inst_to_res:         0
% 3.06/1.07  inst_dismatching_checking_time:         0.
% 3.06/1.07  
% 3.06/1.07  ------ Resolution
% 3.06/1.07  
% 3.06/1.07  res_num_of_clauses:                     0
% 3.06/1.07  res_num_in_passive:                     0
% 3.06/1.07  res_num_in_active:                      0
% 3.06/1.07  res_num_of_loops:                       126
% 3.06/1.07  res_forward_subset_subsumed:            37
% 3.06/1.07  res_backward_subset_subsumed:           0
% 3.06/1.07  res_forward_subsumed:                   3
% 3.06/1.07  res_backward_subsumed:                  0
% 3.06/1.07  res_forward_subsumption_resolution:     3
% 3.06/1.07  res_backward_subsumption_resolution:    0
% 3.06/1.07  res_clause_to_clause_subsumption:       976
% 3.06/1.07  res_orphan_elimination:                 0
% 3.06/1.07  res_tautology_del:                      58
% 3.06/1.07  res_num_eq_res_simplified:              0
% 3.06/1.07  res_num_sel_changes:                    0
% 3.06/1.07  res_moves_from_active_to_pass:          0
% 3.06/1.07  
% 3.06/1.07  ------ Superposition
% 3.06/1.07  
% 3.06/1.07  sup_time_total:                         0.
% 3.06/1.07  sup_time_generating:                    0.
% 3.06/1.07  sup_time_sim_full:                      0.
% 3.06/1.07  sup_time_sim_immed:                     0.
% 3.06/1.07  
% 3.06/1.07  sup_num_of_clauses:                     190
% 3.06/1.07  sup_num_in_active:                      43
% 3.06/1.07  sup_num_in_passive:                     147
% 3.06/1.07  sup_num_of_loops:                       90
% 3.06/1.07  sup_fw_superposition:                   93
% 3.06/1.07  sup_bw_superposition:                   192
% 3.06/1.07  sup_immediate_simplified:               74
% 3.06/1.07  sup_given_eliminated:                   1
% 3.06/1.07  comparisons_done:                       0
% 3.06/1.07  comparisons_avoided:                    7
% 3.06/1.07  
% 3.06/1.07  ------ Simplifications
% 3.06/1.07  
% 3.06/1.07  
% 3.06/1.07  sim_fw_subset_subsumed:                 17
% 3.06/1.07  sim_bw_subset_subsumed:                 6
% 3.06/1.07  sim_fw_subsumed:                        32
% 3.06/1.07  sim_bw_subsumed:                        0
% 3.06/1.07  sim_fw_subsumption_res:                 1
% 3.06/1.07  sim_bw_subsumption_res:                 0
% 3.06/1.07  sim_tautology_del:                      18
% 3.06/1.07  sim_eq_tautology_del:                   8
% 3.06/1.07  sim_eq_res_simp:                        4
% 3.06/1.07  sim_fw_demodulated:                     14
% 3.06/1.07  sim_bw_demodulated:                     46
% 3.06/1.07  sim_light_normalised:                   24
% 3.06/1.07  sim_joinable_taut:                      0
% 3.06/1.07  sim_joinable_simp:                      0
% 3.06/1.07  sim_ac_normalised:                      0
% 3.06/1.07  sim_smt_subsumption:                    0
% 3.06/1.07  
%------------------------------------------------------------------------------
