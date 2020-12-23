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
% DateTime   : Thu Dec  3 11:40:04 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 321 expanded)
%              Number of clauses        :   67 (  99 expanded)
%              Number of leaves         :   22 (  75 expanded)
%              Depth                    :   22
%              Number of atoms          :  384 ( 935 expanded)
%              Number of equality atoms :  151 ( 356 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f4])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f51,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f50])).

fof(f52,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK4) != sK5
        | ~ r1_tarski(k3_subset_1(sK4,sK5),sK5) )
      & ( k2_subset_1(sK4) = sK5
        | r1_tarski(k3_subset_1(sK4,sK5),sK5) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( k2_subset_1(sK4) != sK5
      | ~ r1_tarski(k3_subset_1(sK4,sK5),sK5) )
    & ( k2_subset_1(sK4) = sK5
      | r1_tarski(k3_subset_1(sK4,sK5),sK5) )
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f52])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,
    ( k2_subset_1(sK4) = sK5
    | r1_tarski(k3_subset_1(sK4,sK5),sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f93,f88])).

fof(f110,plain,
    ( k3_subset_1(sK4,k1_xboole_0) = sK5
    | r1_tarski(k3_subset_1(sK4,sK5),sK5) ),
    inference(definition_unfolding,[],[f95,f97])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f108,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f89,f97])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f77])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f54,f77,f77])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f116,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f18,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f120,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f98,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f106,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f96,plain,
    ( k2_subset_1(sK4) != sK5
    | ~ r1_tarski(k3_subset_1(sK4,sK5),sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f109,plain,
    ( k3_subset_1(sK4,k1_xboole_0) != sK5
    | ~ r1_tarski(k3_subset_1(sK4,sK5),sK5) ),
    inference(definition_unfolding,[],[f96,f97])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1331,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1329,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3658,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1329])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2315,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_22])).

cnf(c_2316,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2315])).

cnf(c_3693,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3658,c_2316])).

cnf(c_8295,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = X1
    | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1331,c_3693])).

cnf(c_8333,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8295,c_23])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1310,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1315,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3575,plain,
    ( k3_subset_1(sK4,sK5) = k4_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1310,c_1315])).

cnf(c_37,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK4,sK5),sK5)
    | k3_subset_1(sK4,k1_xboole_0) = sK5 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1311,plain,
    ( k3_subset_1(sK4,k1_xboole_0) = sK5
    | r1_tarski(k3_subset_1(sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1362,plain,
    ( sK5 = sK4
    | r1_tarski(k3_subset_1(sK4,sK5),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1311,c_32])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1325,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2913,plain,
    ( k4_xboole_0(k3_subset_1(sK4,sK5),k4_xboole_0(k3_subset_1(sK4,sK5),sK5)) = k3_subset_1(sK4,sK5)
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_1362,c_1325])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3067,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k3_subset_1(sK4,sK5))) = k3_subset_1(sK4,sK5)
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_2913,c_1])).

cnf(c_3805,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK4,sK5)
    | sK5 = sK4 ),
    inference(demodulation,[status(thm)],[c_3575,c_3067])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1328,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4157,plain,
    ( sK5 = sK4
    | r2_hidden(X0,k4_xboole_0(sK4,sK5)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3805,c_1328])).

cnf(c_5623,plain,
    ( sK5 = sK4
    | r2_hidden(X0,k4_xboole_0(sK4,sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4157,c_1329])).

cnf(c_8512,plain,
    ( k4_xboole_0(sK4,sK5) = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_8333,c_5623])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1316,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2564,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_1316])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1622,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | r2_hidden(sK5,k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1623,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top
    | r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1622])).

cnf(c_34,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1732,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1733,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1732])).

cnf(c_2976,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2564,c_39,c_1623,c_1733])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1320,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2981,plain,
    ( r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2976,c_1320])).

cnf(c_3057,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) = sK5 ),
    inference(superposition,[status(thm)],[c_2981,c_1325])).

cnf(c_3229,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_3057,c_1])).

cnf(c_11138,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) = sK5
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_8512,c_3229])).

cnf(c_1962,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_23])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1979,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1962,c_0])).

cnf(c_20,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1355,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_20,c_23])).

cnf(c_1984,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1979,c_1355])).

cnf(c_11141,plain,
    ( sK5 = sK4 ),
    inference(demodulation,[status(thm)],[c_11138,c_1984])).

cnf(c_36,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK4,sK5),sK5)
    | k3_subset_1(sK4,k1_xboole_0) != sK5 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1312,plain,
    ( k3_subset_1(sK4,k1_xboole_0) != sK5
    | r1_tarski(k3_subset_1(sK4,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1391,plain,
    ( sK5 != sK4
    | r1_tarski(k3_subset_1(sK4,sK5),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1312,c_32])).

cnf(c_3809,plain,
    ( sK5 != sK4
    | r1_tarski(k4_xboole_0(sK4,sK5),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3575,c_1391])).

cnf(c_18078,plain,
    ( sK4 != sK4
    | r1_tarski(k4_xboole_0(sK4,sK4),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11141,c_3809])).

cnf(c_18100,plain,
    ( r1_tarski(k4_xboole_0(sK4,sK4),sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18078])).

cnf(c_1985,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1984,c_1962])).

cnf(c_18102,plain,
    ( r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18100,c_1985])).

cnf(c_9282,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_9285,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9282])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18102,c_9285])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:52:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.74/1.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/1.54  
% 7.74/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.74/1.54  
% 7.74/1.54  ------  iProver source info
% 7.74/1.54  
% 7.74/1.54  git: date: 2020-06-30 10:37:57 +0100
% 7.74/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.74/1.54  git: non_committed_changes: false
% 7.74/1.54  git: last_make_outside_of_git: false
% 7.74/1.54  
% 7.74/1.54  ------ 
% 7.74/1.54  ------ Parsing...
% 7.74/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.54  
% 7.74/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.74/1.54  
% 7.74/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.54  
% 7.74/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.54  ------ Proving...
% 7.74/1.54  ------ Problem Properties 
% 7.74/1.54  
% 7.74/1.54  
% 7.74/1.54  clauses                                 38
% 7.74/1.54  conjectures                             3
% 7.74/1.54  EPR                                     8
% 7.74/1.54  Horn                                    27
% 7.74/1.54  unary                                   9
% 7.74/1.54  binary                                  13
% 7.74/1.54  lits                                    85
% 7.74/1.54  lits eq                                 19
% 7.74/1.54  fd_pure                                 0
% 7.74/1.54  fd_pseudo                               0
% 7.74/1.54  fd_cond                                 0
% 7.74/1.54  fd_pseudo_cond                          9
% 7.74/1.54  AC symbols                              0
% 7.74/1.54  
% 7.74/1.54  ------ Input Options Time Limit: Unbounded
% 7.74/1.54  
% 7.74/1.54  
% 7.74/1.54  ------ 
% 7.74/1.54  Current options:
% 7.74/1.54  ------ 
% 7.74/1.54  
% 7.74/1.54  
% 7.74/1.54  
% 7.74/1.54  
% 7.74/1.54  ------ Proving...
% 7.74/1.54  
% 7.74/1.54  
% 7.74/1.54  % SZS status Theorem for theBenchmark.p
% 7.74/1.54  
% 7.74/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.54  
% 7.74/1.54  fof(f4,axiom,(
% 7.74/1.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f38,plain,(
% 7.74/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.74/1.54    inference(nnf_transformation,[],[f4])).
% 7.74/1.54  
% 7.74/1.54  fof(f39,plain,(
% 7.74/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.74/1.54    inference(flattening,[],[f38])).
% 7.74/1.54  
% 7.74/1.54  fof(f40,plain,(
% 7.74/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.74/1.54    inference(rectify,[],[f39])).
% 7.74/1.54  
% 7.74/1.54  fof(f41,plain,(
% 7.74/1.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.74/1.54    introduced(choice_axiom,[])).
% 7.74/1.54  
% 7.74/1.54  fof(f42,plain,(
% 7.74/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.74/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 7.74/1.54  
% 7.74/1.54  fof(f67,plain,(
% 7.74/1.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.74/1.54    inference(cnf_transformation,[],[f42])).
% 7.74/1.54  
% 7.74/1.54  fof(f11,axiom,(
% 7.74/1.54    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f78,plain,(
% 7.74/1.54    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.74/1.54    inference(cnf_transformation,[],[f11])).
% 7.74/1.54  
% 7.74/1.54  fof(f65,plain,(
% 7.74/1.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.74/1.54    inference(cnf_transformation,[],[f42])).
% 7.74/1.54  
% 7.74/1.54  fof(f115,plain,(
% 7.74/1.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.74/1.54    inference(equality_resolution,[],[f65])).
% 7.74/1.54  
% 7.74/1.54  fof(f2,axiom,(
% 7.74/1.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f23,plain,(
% 7.74/1.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.74/1.54    inference(ennf_transformation,[],[f2])).
% 7.74/1.54  
% 7.74/1.54  fof(f29,plain,(
% 7.74/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.74/1.54    inference(nnf_transformation,[],[f23])).
% 7.74/1.54  
% 7.74/1.54  fof(f30,plain,(
% 7.74/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.74/1.54    inference(rectify,[],[f29])).
% 7.74/1.54  
% 7.74/1.54  fof(f31,plain,(
% 7.74/1.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.74/1.54    introduced(choice_axiom,[])).
% 7.74/1.54  
% 7.74/1.54  fof(f32,plain,(
% 7.74/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.74/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.74/1.54  
% 7.74/1.54  fof(f55,plain,(
% 7.74/1.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.74/1.54    inference(cnf_transformation,[],[f32])).
% 7.74/1.54  
% 7.74/1.54  fof(f9,axiom,(
% 7.74/1.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f76,plain,(
% 7.74/1.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.74/1.54    inference(cnf_transformation,[],[f9])).
% 7.74/1.54  
% 7.74/1.54  fof(f21,conjecture,(
% 7.74/1.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f22,negated_conjecture,(
% 7.74/1.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 7.74/1.54    inference(negated_conjecture,[],[f21])).
% 7.74/1.54  
% 7.74/1.54  fof(f28,plain,(
% 7.74/1.54    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.54    inference(ennf_transformation,[],[f22])).
% 7.74/1.54  
% 7.74/1.54  fof(f50,plain,(
% 7.74/1.54    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.54    inference(nnf_transformation,[],[f28])).
% 7.74/1.54  
% 7.74/1.54  fof(f51,plain,(
% 7.74/1.54    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.54    inference(flattening,[],[f50])).
% 7.74/1.54  
% 7.74/1.54  fof(f52,plain,(
% 7.74/1.54    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK4) != sK5 | ~r1_tarski(k3_subset_1(sK4,sK5),sK5)) & (k2_subset_1(sK4) = sK5 | r1_tarski(k3_subset_1(sK4,sK5),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 7.74/1.54    introduced(choice_axiom,[])).
% 7.74/1.54  
% 7.74/1.54  fof(f53,plain,(
% 7.74/1.54    (k2_subset_1(sK4) != sK5 | ~r1_tarski(k3_subset_1(sK4,sK5),sK5)) & (k2_subset_1(sK4) = sK5 | r1_tarski(k3_subset_1(sK4,sK5),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 7.74/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f52])).
% 7.74/1.54  
% 7.74/1.54  fof(f94,plain,(
% 7.74/1.54    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 7.74/1.54    inference(cnf_transformation,[],[f53])).
% 7.74/1.54  
% 7.74/1.54  fof(f17,axiom,(
% 7.74/1.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f26,plain,(
% 7.74/1.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.54    inference(ennf_transformation,[],[f17])).
% 7.74/1.54  
% 7.74/1.54  fof(f90,plain,(
% 7.74/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.74/1.54    inference(cnf_transformation,[],[f26])).
% 7.74/1.54  
% 7.74/1.54  fof(f95,plain,(
% 7.74/1.54    k2_subset_1(sK4) = sK5 | r1_tarski(k3_subset_1(sK4,sK5),sK5)),
% 7.74/1.54    inference(cnf_transformation,[],[f53])).
% 7.74/1.54  
% 7.74/1.54  fof(f20,axiom,(
% 7.74/1.54    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f93,plain,(
% 7.74/1.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 7.74/1.54    inference(cnf_transformation,[],[f20])).
% 7.74/1.54  
% 7.74/1.54  fof(f15,axiom,(
% 7.74/1.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f88,plain,(
% 7.74/1.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 7.74/1.54    inference(cnf_transformation,[],[f15])).
% 7.74/1.54  
% 7.74/1.54  fof(f97,plain,(
% 7.74/1.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 7.74/1.54    inference(definition_unfolding,[],[f93,f88])).
% 7.74/1.54  
% 7.74/1.54  fof(f110,plain,(
% 7.74/1.54    k3_subset_1(sK4,k1_xboole_0) = sK5 | r1_tarski(k3_subset_1(sK4,sK5),sK5)),
% 7.74/1.54    inference(definition_unfolding,[],[f95,f97])).
% 7.74/1.54  
% 7.74/1.54  fof(f16,axiom,(
% 7.74/1.54    ! [X0] : k2_subset_1(X0) = X0),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f89,plain,(
% 7.74/1.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.74/1.54    inference(cnf_transformation,[],[f16])).
% 7.74/1.54  
% 7.74/1.54  fof(f108,plain,(
% 7.74/1.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 7.74/1.54    inference(definition_unfolding,[],[f89,f97])).
% 7.74/1.54  
% 7.74/1.54  fof(f8,axiom,(
% 7.74/1.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f24,plain,(
% 7.74/1.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.74/1.54    inference(ennf_transformation,[],[f8])).
% 7.74/1.54  
% 7.74/1.54  fof(f75,plain,(
% 7.74/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.74/1.54    inference(cnf_transformation,[],[f24])).
% 7.74/1.54  
% 7.74/1.54  fof(f10,axiom,(
% 7.74/1.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f77,plain,(
% 7.74/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.74/1.54    inference(cnf_transformation,[],[f10])).
% 7.74/1.54  
% 7.74/1.54  fof(f107,plain,(
% 7.74/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.74/1.54    inference(definition_unfolding,[],[f75,f77])).
% 7.74/1.54  
% 7.74/1.54  fof(f1,axiom,(
% 7.74/1.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f54,plain,(
% 7.74/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.74/1.54    inference(cnf_transformation,[],[f1])).
% 7.74/1.54  
% 7.74/1.54  fof(f99,plain,(
% 7.74/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.74/1.54    inference(definition_unfolding,[],[f54,f77,f77])).
% 7.74/1.54  
% 7.74/1.54  fof(f64,plain,(
% 7.74/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.74/1.54    inference(cnf_transformation,[],[f42])).
% 7.74/1.54  
% 7.74/1.54  fof(f116,plain,(
% 7.74/1.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.74/1.54    inference(equality_resolution,[],[f64])).
% 7.74/1.54  
% 7.74/1.54  fof(f14,axiom,(
% 7.74/1.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f25,plain,(
% 7.74/1.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.74/1.54    inference(ennf_transformation,[],[f14])).
% 7.74/1.54  
% 7.74/1.54  fof(f49,plain,(
% 7.74/1.54    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.74/1.54    inference(nnf_transformation,[],[f25])).
% 7.74/1.54  
% 7.74/1.54  fof(f84,plain,(
% 7.74/1.54    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.74/1.54    inference(cnf_transformation,[],[f49])).
% 7.74/1.54  
% 7.74/1.54  fof(f18,axiom,(
% 7.74/1.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f91,plain,(
% 7.74/1.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.74/1.54    inference(cnf_transformation,[],[f18])).
% 7.74/1.54  
% 7.74/1.54  fof(f13,axiom,(
% 7.74/1.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f45,plain,(
% 7.74/1.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.74/1.54    inference(nnf_transformation,[],[f13])).
% 7.74/1.54  
% 7.74/1.54  fof(f46,plain,(
% 7.74/1.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.74/1.54    inference(rectify,[],[f45])).
% 7.74/1.54  
% 7.74/1.54  fof(f47,plain,(
% 7.74/1.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 7.74/1.54    introduced(choice_axiom,[])).
% 7.74/1.54  
% 7.74/1.54  fof(f48,plain,(
% 7.74/1.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.74/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 7.74/1.54  
% 7.74/1.54  fof(f80,plain,(
% 7.74/1.54    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.74/1.54    inference(cnf_transformation,[],[f48])).
% 7.74/1.54  
% 7.74/1.54  fof(f120,plain,(
% 7.74/1.54    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.74/1.54    inference(equality_resolution,[],[f80])).
% 7.74/1.54  
% 7.74/1.54  fof(f6,axiom,(
% 7.74/1.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f73,plain,(
% 7.74/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.74/1.54    inference(cnf_transformation,[],[f6])).
% 7.74/1.54  
% 7.74/1.54  fof(f98,plain,(
% 7.74/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.74/1.54    inference(definition_unfolding,[],[f73,f77])).
% 7.74/1.54  
% 7.74/1.54  fof(f7,axiom,(
% 7.74/1.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f74,plain,(
% 7.74/1.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.74/1.54    inference(cnf_transformation,[],[f7])).
% 7.74/1.54  
% 7.74/1.54  fof(f12,axiom,(
% 7.74/1.54    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.74/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.54  
% 7.74/1.54  fof(f79,plain,(
% 7.74/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.74/1.54    inference(cnf_transformation,[],[f12])).
% 7.74/1.54  
% 7.74/1.54  fof(f106,plain,(
% 7.74/1.54    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 7.74/1.54    inference(definition_unfolding,[],[f74,f79])).
% 7.74/1.54  
% 7.74/1.54  fof(f96,plain,(
% 7.74/1.54    k2_subset_1(sK4) != sK5 | ~r1_tarski(k3_subset_1(sK4,sK5),sK5)),
% 7.74/1.54    inference(cnf_transformation,[],[f53])).
% 7.74/1.54  
% 7.74/1.54  fof(f109,plain,(
% 7.74/1.54    k3_subset_1(sK4,k1_xboole_0) != sK5 | ~r1_tarski(k3_subset_1(sK4,sK5),sK5)),
% 7.74/1.54    inference(definition_unfolding,[],[f96,f97])).
% 7.74/1.54  
% 7.74/1.54  cnf(c_13,plain,
% 7.74/1.54      ( r2_hidden(sK2(X0,X1,X2),X0)
% 7.74/1.54      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.74/1.54      | k4_xboole_0(X0,X1) = X2 ),
% 7.74/1.54      inference(cnf_transformation,[],[f67]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1331,plain,
% 7.74/1.54      ( k4_xboole_0(X0,X1) = X2
% 7.74/1.54      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 7.74/1.54      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_23,plain,
% 7.74/1.54      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.74/1.54      inference(cnf_transformation,[],[f78]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_15,plain,
% 7.74/1.54      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.74/1.54      inference(cnf_transformation,[],[f115]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1329,plain,
% 7.74/1.54      ( r2_hidden(X0,X1) != iProver_top
% 7.74/1.54      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_3658,plain,
% 7.74/1.54      ( r2_hidden(X0,X1) != iProver_top
% 7.74/1.54      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_23,c_1329]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_4,plain,
% 7.74/1.54      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.74/1.54      inference(cnf_transformation,[],[f55]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_22,plain,
% 7.74/1.54      ( r1_tarski(k1_xboole_0,X0) ),
% 7.74/1.54      inference(cnf_transformation,[],[f76]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_2315,plain,
% 7.74/1.54      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 7.74/1.54      inference(resolution,[status(thm)],[c_4,c_22]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_2316,plain,
% 7.74/1.54      ( r2_hidden(X0,X1) = iProver_top
% 7.74/1.54      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_2315]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_3693,plain,
% 7.74/1.54      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.74/1.54      inference(global_propositional_subsumption,
% 7.74/1.54                [status(thm)],
% 7.74/1.54                [c_3658,c_2316]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_8295,plain,
% 7.74/1.54      ( k4_xboole_0(k1_xboole_0,X0) = X1
% 7.74/1.54      | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_1331,c_3693]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_8333,plain,
% 7.74/1.54      ( k1_xboole_0 = X0
% 7.74/1.54      | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 7.74/1.54      inference(demodulation,[status(thm)],[c_8295,c_23]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_38,negated_conjecture,
% 7.74/1.54      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 7.74/1.54      inference(cnf_transformation,[],[f94]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1310,plain,
% 7.74/1.54      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_33,plain,
% 7.74/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.74/1.54      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.74/1.54      inference(cnf_transformation,[],[f90]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1315,plain,
% 7.74/1.54      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.74/1.54      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_3575,plain,
% 7.74/1.54      ( k3_subset_1(sK4,sK5) = k4_xboole_0(sK4,sK5) ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_1310,c_1315]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_37,negated_conjecture,
% 7.74/1.54      ( r1_tarski(k3_subset_1(sK4,sK5),sK5)
% 7.74/1.54      | k3_subset_1(sK4,k1_xboole_0) = sK5 ),
% 7.74/1.54      inference(cnf_transformation,[],[f110]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1311,plain,
% 7.74/1.54      ( k3_subset_1(sK4,k1_xboole_0) = sK5
% 7.74/1.54      | r1_tarski(k3_subset_1(sK4,sK5),sK5) = iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_32,plain,
% 7.74/1.54      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 7.74/1.54      inference(cnf_transformation,[],[f108]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1362,plain,
% 7.74/1.54      ( sK5 = sK4 | r1_tarski(k3_subset_1(sK4,sK5),sK5) = iProver_top ),
% 7.74/1.54      inference(demodulation,[status(thm)],[c_1311,c_32]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_21,plain,
% 7.74/1.54      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.74/1.54      inference(cnf_transformation,[],[f107]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1325,plain,
% 7.74/1.54      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.74/1.54      | r1_tarski(X0,X1) != iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_2913,plain,
% 7.74/1.54      ( k4_xboole_0(k3_subset_1(sK4,sK5),k4_xboole_0(k3_subset_1(sK4,sK5),sK5)) = k3_subset_1(sK4,sK5)
% 7.74/1.54      | sK5 = sK4 ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_1362,c_1325]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1,plain,
% 7.74/1.54      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.74/1.54      inference(cnf_transformation,[],[f99]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_3067,plain,
% 7.74/1.54      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k3_subset_1(sK4,sK5))) = k3_subset_1(sK4,sK5)
% 7.74/1.54      | sK5 = sK4 ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_2913,c_1]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_3805,plain,
% 7.74/1.54      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK4,sK5)
% 7.74/1.54      | sK5 = sK4 ),
% 7.74/1.54      inference(demodulation,[status(thm)],[c_3575,c_3067]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_16,plain,
% 7.74/1.54      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.74/1.54      inference(cnf_transformation,[],[f116]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1328,plain,
% 7.74/1.54      ( r2_hidden(X0,X1) = iProver_top
% 7.74/1.54      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_4157,plain,
% 7.74/1.54      ( sK5 = sK4
% 7.74/1.54      | r2_hidden(X0,k4_xboole_0(sK4,sK5)) != iProver_top
% 7.74/1.54      | r2_hidden(X0,sK5) = iProver_top ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_3805,c_1328]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_5623,plain,
% 7.74/1.54      ( sK5 = sK4 | r2_hidden(X0,k4_xboole_0(sK4,sK5)) != iProver_top ),
% 7.74/1.54      inference(forward_subsumption_resolution,
% 7.74/1.54                [status(thm)],
% 7.74/1.54                [c_4157,c_1329]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_8512,plain,
% 7.74/1.54      ( k4_xboole_0(sK4,sK5) = k1_xboole_0 | sK5 = sK4 ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_8333,c_5623]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_31,plain,
% 7.74/1.54      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.74/1.54      inference(cnf_transformation,[],[f84]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1316,plain,
% 7.74/1.54      ( m1_subset_1(X0,X1) != iProver_top
% 7.74/1.54      | r2_hidden(X0,X1) = iProver_top
% 7.74/1.54      | v1_xboole_0(X1) = iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_2564,plain,
% 7.74/1.54      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
% 7.74/1.54      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_1310,c_1316]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_39,plain,
% 7.74/1.54      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1622,plain,
% 7.74/1.54      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
% 7.74/1.54      | r2_hidden(sK5,k1_zfmisc_1(sK4))
% 7.74/1.54      | v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 7.74/1.54      inference(instantiation,[status(thm)],[c_31]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1623,plain,
% 7.74/1.54      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top
% 7.74/1.54      | r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
% 7.74/1.54      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_1622]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_34,plain,
% 7.74/1.54      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.74/1.54      inference(cnf_transformation,[],[f91]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1732,plain,
% 7.74/1.54      ( ~ v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 7.74/1.54      inference(instantiation,[status(thm)],[c_34]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1733,plain,
% 7.74/1.54      ( v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_1732]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_2976,plain,
% 7.74/1.54      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 7.74/1.54      inference(global_propositional_subsumption,
% 7.74/1.54                [status(thm)],
% 7.74/1.54                [c_2564,c_39,c_1623,c_1733]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_27,plain,
% 7.74/1.54      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.74/1.54      inference(cnf_transformation,[],[f120]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1320,plain,
% 7.74/1.54      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.74/1.54      | r1_tarski(X0,X1) = iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_2981,plain,
% 7.74/1.54      ( r1_tarski(sK5,sK4) = iProver_top ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_2976,c_1320]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_3057,plain,
% 7.74/1.54      ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) = sK5 ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_2981,c_1325]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_3229,plain,
% 7.74/1.54      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = sK5 ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_3057,c_1]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_11138,plain,
% 7.74/1.54      ( k4_xboole_0(sK4,k1_xboole_0) = sK5 | sK5 = sK4 ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_8512,c_3229]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1962,plain,
% 7.74/1.54      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_1,c_23]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_0,plain,
% 7.74/1.54      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.74/1.54      inference(cnf_transformation,[],[f98]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1979,plain,
% 7.74/1.54      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.74/1.54      inference(superposition,[status(thm)],[c_1962,c_0]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_20,plain,
% 7.74/1.54      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 7.74/1.54      inference(cnf_transformation,[],[f106]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1355,plain,
% 7.74/1.54      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.74/1.54      inference(light_normalisation,[status(thm)],[c_20,c_23]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1984,plain,
% 7.74/1.54      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.74/1.54      inference(light_normalisation,[status(thm)],[c_1979,c_1355]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_11141,plain,
% 7.74/1.54      ( sK5 = sK4 ),
% 7.74/1.54      inference(demodulation,[status(thm)],[c_11138,c_1984]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_36,negated_conjecture,
% 7.74/1.54      ( ~ r1_tarski(k3_subset_1(sK4,sK5),sK5)
% 7.74/1.54      | k3_subset_1(sK4,k1_xboole_0) != sK5 ),
% 7.74/1.54      inference(cnf_transformation,[],[f109]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1312,plain,
% 7.74/1.54      ( k3_subset_1(sK4,k1_xboole_0) != sK5
% 7.74/1.54      | r1_tarski(k3_subset_1(sK4,sK5),sK5) != iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1391,plain,
% 7.74/1.54      ( sK5 != sK4 | r1_tarski(k3_subset_1(sK4,sK5),sK5) != iProver_top ),
% 7.74/1.54      inference(demodulation,[status(thm)],[c_1312,c_32]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_3809,plain,
% 7.74/1.54      ( sK5 != sK4 | r1_tarski(k4_xboole_0(sK4,sK5),sK5) != iProver_top ),
% 7.74/1.54      inference(demodulation,[status(thm)],[c_3575,c_1391]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_18078,plain,
% 7.74/1.54      ( sK4 != sK4 | r1_tarski(k4_xboole_0(sK4,sK4),sK4) != iProver_top ),
% 7.74/1.54      inference(demodulation,[status(thm)],[c_11141,c_3809]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_18100,plain,
% 7.74/1.54      ( r1_tarski(k4_xboole_0(sK4,sK4),sK4) != iProver_top ),
% 7.74/1.54      inference(equality_resolution_simp,[status(thm)],[c_18078]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_1985,plain,
% 7.74/1.54      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.74/1.54      inference(demodulation,[status(thm)],[c_1984,c_1962]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_18102,plain,
% 7.74/1.54      ( r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 7.74/1.54      inference(demodulation,[status(thm)],[c_18100,c_1985]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_9282,plain,
% 7.74/1.54      ( r1_tarski(k1_xboole_0,sK4) ),
% 7.74/1.54      inference(instantiation,[status(thm)],[c_22]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(c_9285,plain,
% 7.74/1.54      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 7.74/1.54      inference(predicate_to_equality,[status(thm)],[c_9282]) ).
% 7.74/1.54  
% 7.74/1.54  cnf(contradiction,plain,
% 7.74/1.54      ( $false ),
% 7.74/1.54      inference(minisat,[status(thm)],[c_18102,c_9285]) ).
% 7.74/1.54  
% 7.74/1.54  
% 7.74/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.54  
% 7.74/1.54  ------                               Statistics
% 7.74/1.54  
% 7.74/1.54  ------ Selected
% 7.74/1.54  
% 7.74/1.54  total_time:                             0.725
% 7.74/1.54  
%------------------------------------------------------------------------------
