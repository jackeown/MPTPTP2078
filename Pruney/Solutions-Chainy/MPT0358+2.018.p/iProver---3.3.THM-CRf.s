%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:51 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  163 (4024 expanded)
%              Number of clauses        :   94 (1260 expanded)
%              Number of leaves         :   21 ( 856 expanded)
%              Depth                    :   30
%              Number of atoms          :  492 (15283 expanded)
%              Number of equality atoms :  174 (4039 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f3])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

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

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f57])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f9])).

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

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,
    ( k1_subset_1(sK4) = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f86,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(definition_unfolding,[],[f74,f70])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f32])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f75,plain,
    ( k1_subset_1(sK4) != sK5
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,
    ( k1_xboole_0 != sK5
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(definition_unfolding,[],[f75,f70])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_976,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_954,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_958,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3511,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k3_subset_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_954,c_958])).

cnf(c_4075,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK5,sK4)) = k3_subset_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_0,c_3511])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_959,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1366,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_959])).

cnf(c_1479,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(resolution,[status(thm)],[c_24,c_29])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1490,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1479,c_26])).

cnf(c_1491,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1490])).

cnf(c_1591,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1366,c_1491])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_963,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1596,plain,
    ( r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_963])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_969,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1664,plain,
    ( k3_xboole_0(sK5,sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_1596,c_969])).

cnf(c_4093,plain,
    ( k3_subset_1(sK4,sK5) = k5_xboole_0(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_4075,c_1664])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_955,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1321,plain,
    ( k3_xboole_0(sK5,k3_subset_1(sK4,sK5)) = sK5
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_955,c_969])).

cnf(c_4552,plain,
    ( k3_xboole_0(sK5,k5_xboole_0(sK4,sK5)) = sK5
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4093,c_1321])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_974,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3958,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_974])).

cnf(c_5671,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k5_xboole_0(k5_xboole_0(sK4,sK5),sK5)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_3958])).

cnf(c_331,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_348,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1813,plain,
    ( r2_hidden(X0,k3_subset_1(sK4,sK5))
    | ~ r2_hidden(X0,sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_3,c_28])).

cnf(c_1814,plain,
    ( k1_xboole_0 = sK5
    | r2_hidden(X0,k3_subset_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_332,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2081,plain,
    ( sK5 != X0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_2082,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2081])).

cnf(c_4079,plain,
    ( r2_hidden(X0,k3_subset_1(sK4,sK5)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3511,c_974])).

cnf(c_5953,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5671,c_348,c_1814,c_2082,c_4079])).

cnf(c_8349,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,X0)) = X1
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK5,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_5953])).

cnf(c_1347,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_1582,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_1583,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1602,plain,
    ( r1_tarski(sK5,sK4) ),
    inference(resolution,[status(thm)],[c_1490,c_20])).

cnf(c_1830,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_3,c_1602])).

cnf(c_3543,plain,
    ( ~ r1_xboole_0(sK4,X0)
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,sK5) ),
    inference(resolution,[status(thm)],[c_10,c_1830])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6796,plain,
    ( ~ r1_xboole_0(sK4,X0)
    | ~ r2_hidden(sK0(sK5,X1),X0)
    | r1_tarski(sK5,X1) ),
    inference(resolution,[status(thm)],[c_3543,c_2])).

cnf(c_6822,plain,
    ( ~ r1_xboole_0(sK4,k3_subset_1(sK4,sK5))
    | ~ r2_hidden(sK0(sK5,X0),sK5)
    | r1_tarski(sK5,X0)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_6796,c_1813])).

cnf(c_980,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5961,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_5953])).

cnf(c_5984,plain,
    ( r1_tarski(sK5,X0)
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5961])).

cnf(c_7169,plain,
    ( r1_tarski(sK5,X0)
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6822,c_1582,c_1583,c_5984])).

cnf(c_333,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7190,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(X1,k1_xboole_0)
    | r1_tarski(sK5,X2)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_7169,c_333])).

cnf(c_9164,plain,
    ( r1_tarski(sK5,X0)
    | r1_tarski(sK5,X1)
    | ~ r1_tarski(sK5,sK5)
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7190,c_7169])).

cnf(c_3961,plain,
    ( r2_hidden(X0,k5_xboole_0(sK5,sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_974])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3964,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3961,c_16])).

cnf(c_1831,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1830])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_973,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2303,plain,
    ( r2_hidden(X0,k5_xboole_0(sK5,sK5)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_973])).

cnf(c_2306,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2303,c_16])).

cnf(c_4733,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3964,c_1831,c_2306])).

cnf(c_4740,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_4733])).

cnf(c_4754,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4740])).

cnf(c_2504,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_332,c_331])).

cnf(c_7185,plain,
    ( r1_tarski(sK5,X0)
    | sK5 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7169,c_2504])).

cnf(c_5085,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_333,c_331])).

cnf(c_8571,plain,
    ( r1_tarski(sK5,X0)
    | r1_tarski(sK5,X1)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_7185,c_5085])).

cnf(c_9203,plain,
    ( r1_tarski(sK5,X0)
    | r1_tarski(sK5,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9164,c_4754,c_8571])).

cnf(c_9231,plain,
    ( r1_tarski(sK5,X0) ),
    inference(factoring,[status(thm)],[c_9203])).

cnf(c_27,negated_conjecture,
    ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_9818,plain,
    ( k1_xboole_0 != sK5 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_9231,c_27])).

cnf(c_10904,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,X0)) = X1
    | r2_hidden(sK1(sK5,X0,X1),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8349,c_1582,c_1583,c_9818])).

cnf(c_10920,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10904,c_4733])).

cnf(c_10952,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(sK5,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10920,c_10904])).

cnf(c_10967,plain,
    ( k1_xboole_0 = sK5
    | r2_hidden(sK1(sK5,sK5,sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10952])).

cnf(c_10779,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK1(X2,X3,X0),X1)
    | ~ r2_hidden(sK1(X2,X3,X0),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_10780,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK1(X2,X3,X0),X1) != iProver_top
    | r2_hidden(sK1(X2,X3,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10779])).

cnf(c_10782,plain,
    ( r1_xboole_0(sK5,sK5) != iProver_top
    | r2_hidden(sK1(sK5,sK5,sK5),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10780])).

cnf(c_7196,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_7169,c_3])).

cnf(c_4133,plain,
    ( ~ r2_hidden(X0,k3_subset_1(sK4,sK5))
    | ~ r2_hidden(X0,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4079])).

cnf(c_8800,plain,
    ( ~ r2_hidden(X0,sK5)
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7196,c_1813,c_4133])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8986,plain,
    ( r1_xboole_0(X0,sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_8800,c_11])).

cnf(c_8987,plain,
    ( k1_xboole_0 = sK5
    | r1_xboole_0(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8986])).

cnf(c_8989,plain,
    ( k1_xboole_0 = sK5
    | r1_xboole_0(sK5,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8987])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10967,c_10782,c_9818,c_8989])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.01/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/0.97  
% 4.01/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/0.97  
% 4.01/0.97  ------  iProver source info
% 4.01/0.97  
% 4.01/0.97  git: date: 2020-06-30 10:37:57 +0100
% 4.01/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/0.97  git: non_committed_changes: false
% 4.01/0.97  git: last_make_outside_of_git: false
% 4.01/0.97  
% 4.01/0.97  ------ 
% 4.01/0.97  ------ Parsing...
% 4.01/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/0.97  
% 4.01/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.01/0.97  
% 4.01/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/0.97  
% 4.01/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.01/0.97  ------ Proving...
% 4.01/0.97  ------ Problem Properties 
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  clauses                                 30
% 4.01/0.97  conjectures                             3
% 4.01/0.97  EPR                                     6
% 4.01/0.97  Horn                                    19
% 4.01/0.97  unary                                   4
% 4.01/0.97  binary                                  14
% 4.01/0.97  lits                                    69
% 4.01/0.97  lits eq                                 13
% 4.01/0.97  fd_pure                                 0
% 4.01/0.97  fd_pseudo                               0
% 4.01/0.97  fd_cond                                 0
% 4.01/0.97  fd_pseudo_cond                          5
% 4.01/0.97  AC symbols                              0
% 4.01/0.97  
% 4.01/0.97  ------ Input Options Time Limit: Unbounded
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  ------ 
% 4.01/0.97  Current options:
% 4.01/0.97  ------ 
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  ------ Proving...
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  % SZS status Theorem for theBenchmark.p
% 4.01/0.97  
% 4.01/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/0.97  
% 4.01/0.97  fof(f3,axiom,(
% 4.01/0.97    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f27,plain,(
% 4.01/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.01/0.97    inference(nnf_transformation,[],[f3])).
% 4.01/0.97  
% 4.01/0.97  fof(f28,plain,(
% 4.01/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.01/0.97    inference(flattening,[],[f27])).
% 4.01/0.97  
% 4.01/0.97  fof(f29,plain,(
% 4.01/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.01/0.97    inference(rectify,[],[f28])).
% 4.01/0.97  
% 4.01/0.97  fof(f30,plain,(
% 4.01/0.97    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 4.01/0.97    introduced(choice_axiom,[])).
% 4.01/0.97  
% 4.01/0.97  fof(f31,plain,(
% 4.01/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 4.01/0.97  
% 4.01/0.97  fof(f51,plain,(
% 4.01/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f31])).
% 4.01/0.97  
% 4.01/0.97  fof(f5,axiom,(
% 4.01/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f57,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.01/0.97    inference(cnf_transformation,[],[f5])).
% 4.01/0.97  
% 4.01/0.97  fof(f78,plain,(
% 4.01/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 4.01/0.97    inference(definition_unfolding,[],[f51,f57])).
% 4.01/0.97  
% 4.01/0.97  fof(f1,axiom,(
% 4.01/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f44,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f1])).
% 4.01/0.97  
% 4.01/0.97  fof(f14,conjecture,(
% 4.01/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f15,negated_conjecture,(
% 4.01/0.97    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 4.01/0.97    inference(negated_conjecture,[],[f14])).
% 4.01/0.97  
% 4.01/0.97  fof(f22,plain,(
% 4.01/0.97    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.01/0.97    inference(ennf_transformation,[],[f15])).
% 4.01/0.97  
% 4.01/0.97  fof(f40,plain,(
% 4.01/0.97    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.01/0.97    inference(nnf_transformation,[],[f22])).
% 4.01/0.97  
% 4.01/0.97  fof(f41,plain,(
% 4.01/0.97    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.01/0.97    inference(flattening,[],[f40])).
% 4.01/0.97  
% 4.01/0.97  fof(f42,plain,(
% 4.01/0.97    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))) & (k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 4.01/0.97    introduced(choice_axiom,[])).
% 4.01/0.97  
% 4.01/0.97  fof(f43,plain,(
% 4.01/0.97    (k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))) & (k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 4.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f41,f42])).
% 4.01/0.97  
% 4.01/0.97  fof(f73,plain,(
% 4.01/0.97    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 4.01/0.97    inference(cnf_transformation,[],[f43])).
% 4.01/0.97  
% 4.01/0.97  fof(f12,axiom,(
% 4.01/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f21,plain,(
% 4.01/0.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.01/0.97    inference(ennf_transformation,[],[f12])).
% 4.01/0.97  
% 4.01/0.97  fof(f71,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.01/0.97    inference(cnf_transformation,[],[f21])).
% 4.01/0.97  
% 4.01/0.97  fof(f84,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.01/0.97    inference(definition_unfolding,[],[f71,f57])).
% 4.01/0.97  
% 4.01/0.97  fof(f10,axiom,(
% 4.01/0.97    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f20,plain,(
% 4.01/0.97    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 4.01/0.97    inference(ennf_transformation,[],[f10])).
% 4.01/0.97  
% 4.01/0.97  fof(f39,plain,(
% 4.01/0.97    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 4.01/0.97    inference(nnf_transformation,[],[f20])).
% 4.01/0.97  
% 4.01/0.97  fof(f66,plain,(
% 4.01/0.97    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f39])).
% 4.01/0.97  
% 4.01/0.97  fof(f13,axiom,(
% 4.01/0.97    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f72,plain,(
% 4.01/0.97    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 4.01/0.97    inference(cnf_transformation,[],[f13])).
% 4.01/0.97  
% 4.01/0.97  fof(f9,axiom,(
% 4.01/0.97    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f35,plain,(
% 4.01/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.01/0.97    inference(nnf_transformation,[],[f9])).
% 4.01/0.97  
% 4.01/0.97  fof(f36,plain,(
% 4.01/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.01/0.97    inference(rectify,[],[f35])).
% 4.01/0.97  
% 4.01/0.97  fof(f37,plain,(
% 4.01/0.97    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 4.01/0.97    introduced(choice_axiom,[])).
% 4.01/0.97  
% 4.01/0.97  fof(f38,plain,(
% 4.01/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 4.01/0.97  
% 4.01/0.97  fof(f62,plain,(
% 4.01/0.97    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 4.01/0.97    inference(cnf_transformation,[],[f38])).
% 4.01/0.97  
% 4.01/0.97  fof(f91,plain,(
% 4.01/0.97    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 4.01/0.97    inference(equality_resolution,[],[f62])).
% 4.01/0.97  
% 4.01/0.97  fof(f6,axiom,(
% 4.01/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f19,plain,(
% 4.01/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.01/0.97    inference(ennf_transformation,[],[f6])).
% 4.01/0.97  
% 4.01/0.97  fof(f58,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f19])).
% 4.01/0.97  
% 4.01/0.97  fof(f74,plain,(
% 4.01/0.97    k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 4.01/0.97    inference(cnf_transformation,[],[f43])).
% 4.01/0.97  
% 4.01/0.97  fof(f11,axiom,(
% 4.01/0.97    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f70,plain,(
% 4.01/0.97    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f11])).
% 4.01/0.97  
% 4.01/0.97  fof(f86,plain,(
% 4.01/0.97    k1_xboole_0 = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 4.01/0.97    inference(definition_unfolding,[],[f74,f70])).
% 4.01/0.97  
% 4.01/0.97  fof(f49,plain,(
% 4.01/0.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.01/0.97    inference(cnf_transformation,[],[f31])).
% 4.01/0.97  
% 4.01/0.97  fof(f80,plain,(
% 4.01/0.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 4.01/0.97    inference(definition_unfolding,[],[f49,f57])).
% 4.01/0.97  
% 4.01/0.97  fof(f88,plain,(
% 4.01/0.97    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 4.01/0.97    inference(equality_resolution,[],[f80])).
% 4.01/0.97  
% 4.01/0.97  fof(f2,axiom,(
% 4.01/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f17,plain,(
% 4.01/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.01/0.97    inference(ennf_transformation,[],[f2])).
% 4.01/0.97  
% 4.01/0.97  fof(f23,plain,(
% 4.01/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.01/0.97    inference(nnf_transformation,[],[f17])).
% 4.01/0.97  
% 4.01/0.97  fof(f24,plain,(
% 4.01/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.01/0.97    inference(rectify,[],[f23])).
% 4.01/0.97  
% 4.01/0.97  fof(f25,plain,(
% 4.01/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.01/0.97    introduced(choice_axiom,[])).
% 4.01/0.97  
% 4.01/0.97  fof(f26,plain,(
% 4.01/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 4.01/0.97  
% 4.01/0.97  fof(f45,plain,(
% 4.01/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f26])).
% 4.01/0.97  
% 4.01/0.97  fof(f4,axiom,(
% 4.01/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f16,plain,(
% 4.01/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.01/0.97    inference(rectify,[],[f4])).
% 4.01/0.97  
% 4.01/0.97  fof(f18,plain,(
% 4.01/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.01/0.97    inference(ennf_transformation,[],[f16])).
% 4.01/0.97  
% 4.01/0.97  fof(f32,plain,(
% 4.01/0.97    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 4.01/0.97    introduced(choice_axiom,[])).
% 4.01/0.97  
% 4.01/0.97  fof(f33,plain,(
% 4.01/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f32])).
% 4.01/0.97  
% 4.01/0.97  fof(f56,plain,(
% 4.01/0.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f33])).
% 4.01/0.97  
% 4.01/0.97  fof(f46,plain,(
% 4.01/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f26])).
% 4.01/0.97  
% 4.01/0.97  fof(f8,axiom,(
% 4.01/0.97    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f61,plain,(
% 4.01/0.97    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 4.01/0.97    inference(cnf_transformation,[],[f8])).
% 4.01/0.97  
% 4.01/0.97  fof(f48,plain,(
% 4.01/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.01/0.97    inference(cnf_transformation,[],[f31])).
% 4.01/0.97  
% 4.01/0.97  fof(f81,plain,(
% 4.01/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 4.01/0.97    inference(definition_unfolding,[],[f48,f57])).
% 4.01/0.97  
% 4.01/0.97  fof(f89,plain,(
% 4.01/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 4.01/0.97    inference(equality_resolution,[],[f81])).
% 4.01/0.97  
% 4.01/0.97  fof(f75,plain,(
% 4.01/0.97    k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 4.01/0.97    inference(cnf_transformation,[],[f43])).
% 4.01/0.97  
% 4.01/0.97  fof(f85,plain,(
% 4.01/0.97    k1_xboole_0 != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 4.01/0.97    inference(definition_unfolding,[],[f75,f70])).
% 4.01/0.97  
% 4.01/0.97  fof(f55,plain,(
% 4.01/0.97    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f33])).
% 4.01/0.97  
% 4.01/0.97  cnf(c_6,plain,
% 4.01/0.97      ( r2_hidden(sK1(X0,X1,X2),X0)
% 4.01/0.97      | r2_hidden(sK1(X0,X1,X2),X2)
% 4.01/0.97      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 4.01/0.97      inference(cnf_transformation,[],[f78]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_976,plain,
% 4.01/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 4.01/0.97      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 4.01/0.97      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_0,plain,
% 4.01/0.97      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 4.01/0.97      inference(cnf_transformation,[],[f44]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_29,negated_conjecture,
% 4.01/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 4.01/0.97      inference(cnf_transformation,[],[f73]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_954,plain,
% 4.01/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_25,plain,
% 4.01/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.01/0.97      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 4.01/0.97      inference(cnf_transformation,[],[f84]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_958,plain,
% 4.01/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 4.01/0.97      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_3511,plain,
% 4.01/0.97      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k3_subset_1(sK4,sK5) ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_954,c_958]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_4075,plain,
% 4.01/0.97      ( k5_xboole_0(sK4,k3_xboole_0(sK5,sK4)) = k3_subset_1(sK4,sK5) ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_0,c_3511]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_24,plain,
% 4.01/0.97      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 4.01/0.97      inference(cnf_transformation,[],[f66]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_959,plain,
% 4.01/0.97      ( m1_subset_1(X0,X1) != iProver_top
% 4.01/0.97      | r2_hidden(X0,X1) = iProver_top
% 4.01/0.97      | v1_xboole_0(X1) = iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_1366,plain,
% 4.01/0.97      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
% 4.01/0.97      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_954,c_959]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_1479,plain,
% 4.01/0.97      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) | v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 4.01/0.97      inference(resolution,[status(thm)],[c_24,c_29]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_26,plain,
% 4.01/0.97      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 4.01/0.97      inference(cnf_transformation,[],[f72]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_1490,plain,
% 4.01/0.97      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
% 4.01/0.97      inference(forward_subsumption_resolution,
% 4.01/0.97                [status(thm)],
% 4.01/0.97                [c_1479,c_26]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_1491,plain,
% 4.01/0.97      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_1490]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_1591,plain,
% 4.01/0.97      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 4.01/0.97      inference(global_propositional_subsumption,
% 4.01/0.97                [status(thm)],
% 4.01/0.97                [c_1366,c_1491]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_20,plain,
% 4.01/0.97      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.01/0.97      inference(cnf_transformation,[],[f91]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_963,plain,
% 4.01/0.97      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.01/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_1596,plain,
% 4.01/0.97      ( r1_tarski(sK5,sK4) = iProver_top ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_1591,c_963]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_13,plain,
% 4.01/0.97      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 4.01/0.97      inference(cnf_transformation,[],[f58]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_969,plain,
% 4.01/0.97      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_1664,plain,
% 4.01/0.97      ( k3_xboole_0(sK5,sK4) = sK5 ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_1596,c_969]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_4093,plain,
% 4.01/0.97      ( k3_subset_1(sK4,sK5) = k5_xboole_0(sK4,sK5) ),
% 4.01/0.97      inference(light_normalisation,[status(thm)],[c_4075,c_1664]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_28,negated_conjecture,
% 4.01/0.97      ( r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 = sK5 ),
% 4.01/0.97      inference(cnf_transformation,[],[f86]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_955,plain,
% 4.01/0.97      ( k1_xboole_0 = sK5
% 4.01/0.97      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_1321,plain,
% 4.01/0.97      ( k3_xboole_0(sK5,k3_subset_1(sK4,sK5)) = sK5 | sK5 = k1_xboole_0 ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_955,c_969]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_4552,plain,
% 4.01/0.97      ( k3_xboole_0(sK5,k5_xboole_0(sK4,sK5)) = sK5 | sK5 = k1_xboole_0 ),
% 4.01/0.97      inference(demodulation,[status(thm)],[c_4093,c_1321]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_8,plain,
% 4.01/0.97      ( ~ r2_hidden(X0,X1)
% 4.01/0.97      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 4.01/0.97      inference(cnf_transformation,[],[f88]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_974,plain,
% 4.01/0.98      ( r2_hidden(X0,X1) != iProver_top
% 4.01/0.98      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3958,plain,
% 4.01/0.98      ( r2_hidden(X0,X1) != iProver_top
% 4.01/0.98      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_0,c_974]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5671,plain,
% 4.01/0.98      ( sK5 = k1_xboole_0
% 4.01/0.98      | r2_hidden(X0,k5_xboole_0(k5_xboole_0(sK4,sK5),sK5)) != iProver_top
% 4.01/0.98      | r2_hidden(X0,sK5) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_4552,c_3958]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_331,plain,( X0 = X0 ),theory(equality) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_348,plain,
% 4.01/0.98      ( sK5 = sK5 ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_331]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3,plain,
% 4.01/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 4.01/0.98      inference(cnf_transformation,[],[f45]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1813,plain,
% 4.01/0.98      ( r2_hidden(X0,k3_subset_1(sK4,sK5))
% 4.01/0.98      | ~ r2_hidden(X0,sK5)
% 4.01/0.98      | k1_xboole_0 = sK5 ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_3,c_28]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1814,plain,
% 4.01/0.98      ( k1_xboole_0 = sK5
% 4.01/0.98      | r2_hidden(X0,k3_subset_1(sK4,sK5)) = iProver_top
% 4.01/0.98      | r2_hidden(X0,sK5) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_1813]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_332,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2081,plain,
% 4.01/0.98      ( sK5 != X0 | sK5 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_332]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2082,plain,
% 4.01/0.98      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_2081]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4079,plain,
% 4.01/0.98      ( r2_hidden(X0,k3_subset_1(sK4,sK5)) != iProver_top
% 4.01/0.98      | r2_hidden(X0,sK5) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_3511,c_974]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5953,plain,
% 4.01/0.98      ( sK5 = k1_xboole_0 | r2_hidden(X0,sK5) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_5671,c_348,c_1814,c_2082,c_4079]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8349,plain,
% 4.01/0.98      ( k5_xboole_0(sK5,k3_xboole_0(sK5,X0)) = X1
% 4.01/0.98      | sK5 = k1_xboole_0
% 4.01/0.98      | r2_hidden(sK1(sK5,X0,X1),X1) = iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_976,c_5953]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1347,plain,
% 4.01/0.98      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_332]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1582,plain,
% 4.01/0.98      ( sK5 != k1_xboole_0
% 4.01/0.98      | k1_xboole_0 = sK5
% 4.01/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_1347]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1583,plain,
% 4.01/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_331]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10,plain,
% 4.01/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f56]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1602,plain,
% 4.01/0.98      ( r1_tarski(sK5,sK4) ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_1490,c_20]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1830,plain,
% 4.01/0.98      ( r2_hidden(X0,sK4) | ~ r2_hidden(X0,sK5) ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_3,c_1602]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3543,plain,
% 4.01/0.98      ( ~ r1_xboole_0(sK4,X0)
% 4.01/0.98      | ~ r2_hidden(X1,X0)
% 4.01/0.98      | ~ r2_hidden(X1,sK5) ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_10,c_1830]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2,plain,
% 4.01/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f46]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6796,plain,
% 4.01/0.98      ( ~ r1_xboole_0(sK4,X0)
% 4.01/0.98      | ~ r2_hidden(sK0(sK5,X1),X0)
% 4.01/0.98      | r1_tarski(sK5,X1) ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_3543,c_2]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6822,plain,
% 4.01/0.98      ( ~ r1_xboole_0(sK4,k3_subset_1(sK4,sK5))
% 4.01/0.98      | ~ r2_hidden(sK0(sK5,X0),sK5)
% 4.01/0.98      | r1_tarski(sK5,X0)
% 4.01/0.98      | k1_xboole_0 = sK5 ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_6796,c_1813]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_980,plain,
% 4.01/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 4.01/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5961,plain,
% 4.01/0.98      ( sK5 = k1_xboole_0 | r1_tarski(sK5,X0) = iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_980,c_5953]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5984,plain,
% 4.01/0.98      ( r1_tarski(sK5,X0) | sK5 = k1_xboole_0 ),
% 4.01/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_5961]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7169,plain,
% 4.01/0.98      ( r1_tarski(sK5,X0) | k1_xboole_0 = sK5 ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_6822,c_1582,c_1583,c_5984]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_333,plain,
% 4.01/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.01/0.98      theory(equality) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7190,plain,
% 4.01/0.98      ( ~ r1_tarski(X0,sK5)
% 4.01/0.98      | r1_tarski(X1,k1_xboole_0)
% 4.01/0.98      | r1_tarski(sK5,X2)
% 4.01/0.98      | X1 != X0 ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_7169,c_333]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9164,plain,
% 4.01/0.98      ( r1_tarski(sK5,X0)
% 4.01/0.98      | r1_tarski(sK5,X1)
% 4.01/0.98      | ~ r1_tarski(sK5,sK5)
% 4.01/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_7190,c_7169]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3961,plain,
% 4.01/0.98      ( r2_hidden(X0,k5_xboole_0(sK5,sK5)) != iProver_top
% 4.01/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1664,c_974]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_16,plain,
% 4.01/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.01/0.98      inference(cnf_transformation,[],[f61]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3964,plain,
% 4.01/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 4.01/0.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(demodulation,[status(thm)],[c_3961,c_16]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1831,plain,
% 4.01/0.98      ( r2_hidden(X0,sK4) = iProver_top
% 4.01/0.98      | r2_hidden(X0,sK5) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_1830]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9,plain,
% 4.01/0.98      ( r2_hidden(X0,X1)
% 4.01/0.98      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 4.01/0.98      inference(cnf_transformation,[],[f89]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_973,plain,
% 4.01/0.98      ( r2_hidden(X0,X1) = iProver_top
% 4.01/0.98      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2303,plain,
% 4.01/0.98      ( r2_hidden(X0,k5_xboole_0(sK5,sK5)) != iProver_top
% 4.01/0.98      | r2_hidden(X0,sK5) = iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1664,c_973]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2306,plain,
% 4.01/0.98      ( r2_hidden(X0,sK5) = iProver_top
% 4.01/0.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(demodulation,[status(thm)],[c_2303,c_16]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4733,plain,
% 4.01/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_3964,c_1831,c_2306]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4740,plain,
% 4.01/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_980,c_4733]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4754,plain,
% 4.01/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 4.01/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4740]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2504,plain,
% 4.01/0.98      ( X0 != X1 | X1 = X0 ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_332,c_331]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7185,plain,
% 4.01/0.98      ( r1_tarski(sK5,X0) | sK5 = k1_xboole_0 ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_7169,c_2504]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5085,plain,
% 4.01/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_333,c_331]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8571,plain,
% 4.01/0.98      ( r1_tarski(sK5,X0)
% 4.01/0.98      | r1_tarski(sK5,X1)
% 4.01/0.98      | ~ r1_tarski(k1_xboole_0,X0) ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_7185,c_5085]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9203,plain,
% 4.01/0.98      ( r1_tarski(sK5,X0) | r1_tarski(sK5,X1) ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_9164,c_4754,c_8571]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9231,plain,
% 4.01/0.98      ( r1_tarski(sK5,X0) ),
% 4.01/0.98      inference(factoring,[status(thm)],[c_9203]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_27,negated_conjecture,
% 4.01/0.98      ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 != sK5 ),
% 4.01/0.98      inference(cnf_transformation,[],[f85]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9818,plain,
% 4.01/0.98      ( k1_xboole_0 != sK5 ),
% 4.01/0.98      inference(backward_subsumption_resolution,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_9231,c_27]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10904,plain,
% 4.01/0.98      ( k5_xboole_0(sK5,k3_xboole_0(sK5,X0)) = X1
% 4.01/0.98      | r2_hidden(sK1(sK5,X0,X1),X1) = iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_8349,c_1582,c_1583,c_9818]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10920,plain,
% 4.01/0.98      ( k5_xboole_0(sK5,k3_xboole_0(sK5,X0)) = k1_xboole_0 ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_10904,c_4733]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10952,plain,
% 4.01/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK1(sK5,X1,X0),X0) = iProver_top ),
% 4.01/0.98      inference(demodulation,[status(thm)],[c_10920,c_10904]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10967,plain,
% 4.01/0.98      ( k1_xboole_0 = sK5
% 4.01/0.98      | r2_hidden(sK1(sK5,sK5,sK5),sK5) = iProver_top ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_10952]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10779,plain,
% 4.01/0.98      ( ~ r1_xboole_0(X0,X1)
% 4.01/0.98      | ~ r2_hidden(sK1(X2,X3,X0),X1)
% 4.01/0.98      | ~ r2_hidden(sK1(X2,X3,X0),X0) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10780,plain,
% 4.01/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 4.01/0.98      | r2_hidden(sK1(X2,X3,X0),X1) != iProver_top
% 4.01/0.98      | r2_hidden(sK1(X2,X3,X0),X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_10779]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10782,plain,
% 4.01/0.98      ( r1_xboole_0(sK5,sK5) != iProver_top
% 4.01/0.98      | r2_hidden(sK1(sK5,sK5,sK5),sK5) != iProver_top ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_10780]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7196,plain,
% 4.01/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,sK5) | k1_xboole_0 = sK5 ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_7169,c_3]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4133,plain,
% 4.01/0.98      ( ~ r2_hidden(X0,k3_subset_1(sK4,sK5)) | ~ r2_hidden(X0,sK5) ),
% 4.01/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4079]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8800,plain,
% 4.01/0.98      ( ~ r2_hidden(X0,sK5) | k1_xboole_0 = sK5 ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_7196,c_1813,c_4133]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_11,plain,
% 4.01/0.98      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f55]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8986,plain,
% 4.01/0.98      ( r1_xboole_0(X0,sK5) | k1_xboole_0 = sK5 ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_8800,c_11]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8987,plain,
% 4.01/0.98      ( k1_xboole_0 = sK5 | r1_xboole_0(X0,sK5) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_8986]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8989,plain,
% 4.01/0.98      ( k1_xboole_0 = sK5 | r1_xboole_0(sK5,sK5) = iProver_top ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_8987]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(contradiction,plain,
% 4.01/0.98      ( $false ),
% 4.01/0.98      inference(minisat,[status(thm)],[c_10967,c_10782,c_9818,c_8989]) ).
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  ------                               Statistics
% 4.01/0.98  
% 4.01/0.98  ------ Selected
% 4.01/0.98  
% 4.01/0.98  total_time:                             0.343
% 4.01/0.98  
%------------------------------------------------------------------------------
