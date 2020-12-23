%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:03 EST 2020

% Result     : Theorem 11.87s
% Output     : CNFRefutation 11.87s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 563 expanded)
%              Number of clauses        :   94 ( 253 expanded)
%              Number of leaves         :   20 ( 138 expanded)
%              Depth                    :   22
%              Number of atoms          :  478 (1994 expanded)
%              Number of equality atoms :  187 ( 710 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f59,f48])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,
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

fof(f36,plain,
    ( ( k2_subset_1(sK3) != sK4
      | ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) )
    & ( k2_subset_1(sK3) = sK4
      | r1_tarski(k3_subset_1(sK3,sK4),sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f35])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f62,plain,
    ( k2_subset_1(sK3) = sK4
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,
    ( k2_subset_1(sK3) != sK4
    | ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1287,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_47443,plain,
    ( k3_xboole_0(sK3,X0) != X1
    | sK4 != X1
    | sK4 = k3_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_47444,plain,
    ( k3_xboole_0(sK3,sK4) != sK4
    | sK4 = k3_xboole_0(sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_47443])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1763,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_356,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_357,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_1824,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
    inference(equality_resolution,[status(thm)],[c_357])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1758,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3074,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1824,c_1758])).

cnf(c_1290,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1286,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3120,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1290,c_1286])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | k2_subset_1(sK3) = sK4 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6120,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | r1_tarski(k2_subset_1(sK3),X0)
    | ~ r1_tarski(sK4,X0) ),
    inference(resolution,[status(thm)],[c_3120,c_24])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6773,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_subset_1(sK3))
    | r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | ~ r1_tarski(sK4,X1) ),
    inference(resolution,[status(thm)],[c_6120,c_4])).

cnf(c_1301,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1286])).

cnf(c_1292,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1835,plain,
    ( X0 != sK3
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_1836,plain,
    ( k1_zfmisc_1(sK4) = k1_zfmisc_1(sK3)
    | sK4 != sK3 ),
    inference(instantiation,[status(thm)],[c_1835])).

cnf(c_20,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2101,plain,
    ( k2_subset_1(sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2409,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_2767,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2409])).

cnf(c_2769,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2767])).

cnf(c_2768,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1286])).

cnf(c_1879,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | k3_subset_1(sK3,sK4) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_4313,plain,
    ( ~ r1_tarski(k3_subset_1(X0,X1),X2)
    | r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | k3_subset_1(sK3,sK4) != k3_subset_1(X0,X1)
    | sK4 != X2 ),
    inference(instantiation,[status(thm)],[c_1879])).

cnf(c_4316,plain,
    ( ~ r1_tarski(k3_subset_1(sK4,sK4),sK4)
    | r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | k3_subset_1(sK3,sK4) != k3_subset_1(sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4313])).

cnf(c_1294,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_4314,plain,
    ( k3_subset_1(sK3,sK4) = k3_subset_1(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_4319,plain,
    ( k3_subset_1(sK3,sK4) = k3_subset_1(sK4,sK4)
    | sK4 != sK4
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_4314])).

cnf(c_4868,plain,
    ( k2_subset_1(sK3) != sK3
    | sK3 = k2_subset_1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2767])).

cnf(c_2401,plain,
    ( sK4 != X0
    | sK4 = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_4977,plain,
    ( sK4 != k2_subset_1(sK3)
    | sK4 = sK3
    | sK3 != k2_subset_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2401])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1756,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2351,plain,
    ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1763,c_1756])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1764,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5945,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2351,c_1764])).

cnf(c_5985,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5945])).

cnf(c_5987,plain,
    ( r1_tarski(k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_5985])).

cnf(c_2562,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1287,c_1286])).

cnf(c_6034,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | sK4 = k2_subset_1(sK3) ),
    inference(resolution,[status(thm)],[c_2562,c_24])).

cnf(c_6041,plain,
    ( k3_subset_1(X0,sK4) = k5_xboole_0(X0,k3_xboole_0(X0,sK4))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(resolution,[status(thm)],[c_2562,c_357])).

cnf(c_11984,plain,
    ( r1_tarski(k3_subset_1(X0,sK4),X1)
    | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,sK4)),X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(resolution,[status(thm)],[c_6041,c_3120])).

cnf(c_11998,plain,
    ( r1_tarski(k3_subset_1(sK4,sK4),sK4)
    | ~ r1_tarski(k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)),sK4)
    | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11984])).

cnf(c_12011,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6773,c_1301,c_1836,c_2101,c_2769,c_2768,c_4316,c_4319,c_4868,c_4977,c_5987,c_6034,c_11998])).

cnf(c_12025,plain,
    ( ~ r2_hidden(X0,k3_subset_1(sK3,sK4))
    | r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_12011,c_4])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | k2_subset_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_190,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | k2_subset_1(sK3) = sK4 ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_610,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k3_subset_1(sK3,sK4) != X1
    | k2_subset_1(sK3) = sK4
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_190])).

cnf(c_611,plain,
    ( ~ r2_hidden(X0,k3_subset_1(sK3,sK4))
    | r2_hidden(X0,sK4)
    | k2_subset_1(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1757,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3076,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1824,c_1757])).

cnf(c_3083,plain,
    ( ~ r2_hidden(X0,k3_subset_1(sK3,sK4))
    | ~ r2_hidden(X0,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3076])).

cnf(c_19481,plain,
    ( ~ r2_hidden(X0,k3_subset_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12025,c_23,c_611,c_1301,c_1836,c_2101,c_2769,c_2768,c_3083,c_4316,c_4319,c_4868,c_4977,c_5987,c_6034,c_11998])).

cnf(c_19483,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19481])).

cnf(c_32430,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3074,c_19483])).

cnf(c_32436,plain,
    ( r2_hidden(sK0(sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1763,c_32430])).

cnf(c_32462,plain,
    ( r2_hidden(sK0(sK3,X0),sK4)
    | r1_tarski(sK3,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_32436])).

cnf(c_32464,plain,
    ( r2_hidden(sK0(sK3,sK4),sK4)
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_32462])).

cnf(c_1941,plain,
    ( k2_subset_1(sK3) != X0
    | k2_subset_1(sK3) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_17754,plain,
    ( k2_subset_1(sK3) != k3_xboole_0(sK3,X0)
    | k2_subset_1(sK3) = sK4
    | sK4 != k3_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1941])).

cnf(c_17755,plain,
    ( k2_subset_1(sK3) != k3_xboole_0(sK3,sK4)
    | k2_subset_1(sK3) = sK4
    | sK4 != k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_17754])).

cnf(c_4690,plain,
    ( ~ r2_hidden(sK0(sK3,X0),X0)
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4702,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),sK4)
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_4690])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_343,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_344,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_22,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_350,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_344,c_22])).

cnf(c_1748,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1751,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2131,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1751])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1755,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3344,plain,
    ( k3_xboole_0(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_2131,c_1755])).

cnf(c_3519,plain,
    ( k3_xboole_0(sK3,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_0,c_3344])).

cnf(c_2655,plain,
    ( ~ r1_tarski(sK3,X0)
    | k3_xboole_0(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2658,plain,
    ( ~ r1_tarski(sK3,sK4)
    | k3_xboole_0(sK3,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_2655])).

cnf(c_2104,plain,
    ( X0 != X1
    | k2_subset_1(sK3) != X1
    | k2_subset_1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_2417,plain,
    ( X0 != sK3
    | k2_subset_1(sK3) = X0
    | k2_subset_1(sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_2104])).

cnf(c_2654,plain,
    ( k3_xboole_0(sK3,X0) != sK3
    | k2_subset_1(sK3) = k3_xboole_0(sK3,X0)
    | k2_subset_1(sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_2656,plain,
    ( k3_xboole_0(sK3,sK4) != sK3
    | k2_subset_1(sK3) = k3_xboole_0(sK3,sK4)
    | k2_subset_1(sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_2654])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47444,c_32464,c_17755,c_12011,c_4702,c_3519,c_2658,c_2656,c_2101,c_1301,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:41:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.87/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.87/1.98  
% 11.87/1.98  ------  iProver source info
% 11.87/1.98  
% 11.87/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.87/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.87/1.98  git: non_committed_changes: false
% 11.87/1.98  git: last_make_outside_of_git: false
% 11.87/1.98  
% 11.87/1.98  ------ 
% 11.87/1.98  ------ Parsing...
% 11.87/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/1.98  ------ Proving...
% 11.87/1.98  ------ Problem Properties 
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  clauses                                 22
% 11.87/1.98  conjectures                             2
% 11.87/1.98  EPR                                     1
% 11.87/1.98  Horn                                    15
% 11.87/1.98  unary                                   4
% 11.87/1.98  binary                                  11
% 11.87/1.98  lits                                    48
% 11.87/1.98  lits eq                                 14
% 11.87/1.98  fd_pure                                 0
% 11.87/1.98  fd_pseudo                               0
% 11.87/1.98  fd_cond                                 0
% 11.87/1.98  fd_pseudo_cond                          5
% 11.87/1.98  AC symbols                              0
% 11.87/1.98  
% 11.87/1.98  ------ Input Options Time Limit: Unbounded
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  ------ 
% 11.87/1.98  Current options:
% 11.87/1.98  ------ 
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  ------ Proving...
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  % SZS status Theorem for theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  fof(f3,axiom,(
% 11.87/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f14,plain,(
% 11.87/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.87/1.98    inference(ennf_transformation,[],[f3])).
% 11.87/1.98  
% 11.87/1.98  fof(f19,plain,(
% 11.87/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.87/1.98    inference(nnf_transformation,[],[f14])).
% 11.87/1.98  
% 11.87/1.98  fof(f20,plain,(
% 11.87/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.87/1.98    inference(rectify,[],[f19])).
% 11.87/1.98  
% 11.87/1.98  fof(f21,plain,(
% 11.87/1.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.87/1.98    introduced(choice_axiom,[])).
% 11.87/1.98  
% 11.87/1.98  fof(f22,plain,(
% 11.87/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.87/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 11.87/1.98  
% 11.87/1.98  fof(f40,plain,(
% 11.87/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f22])).
% 11.87/1.98  
% 11.87/1.98  fof(f10,axiom,(
% 11.87/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f17,plain,(
% 11.87/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.87/1.98    inference(ennf_transformation,[],[f10])).
% 11.87/1.98  
% 11.87/1.98  fof(f59,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.87/1.98    inference(cnf_transformation,[],[f17])).
% 11.87/1.98  
% 11.87/1.98  fof(f5,axiom,(
% 11.87/1.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f48,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f5])).
% 11.87/1.98  
% 11.87/1.98  fof(f70,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.87/1.98    inference(definition_unfolding,[],[f59,f48])).
% 11.87/1.98  
% 11.87/1.98  fof(f12,conjecture,(
% 11.87/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f13,negated_conjecture,(
% 11.87/1.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 11.87/1.98    inference(negated_conjecture,[],[f12])).
% 11.87/1.98  
% 11.87/1.98  fof(f18,plain,(
% 11.87/1.98    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.87/1.98    inference(ennf_transformation,[],[f13])).
% 11.87/1.98  
% 11.87/1.98  fof(f33,plain,(
% 11.87/1.98    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.87/1.98    inference(nnf_transformation,[],[f18])).
% 11.87/1.98  
% 11.87/1.98  fof(f34,plain,(
% 11.87/1.98    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.87/1.98    inference(flattening,[],[f33])).
% 11.87/1.98  
% 11.87/1.98  fof(f35,plain,(
% 11.87/1.98    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK3) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)) & (k2_subset_1(sK3) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 11.87/1.98    introduced(choice_axiom,[])).
% 11.87/1.98  
% 11.87/1.98  fof(f36,plain,(
% 11.87/1.98    (k2_subset_1(sK3) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)) & (k2_subset_1(sK3) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 11.87/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f35])).
% 11.87/1.98  
% 11.87/1.98  fof(f61,plain,(
% 11.87/1.98    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 11.87/1.98    inference(cnf_transformation,[],[f36])).
% 11.87/1.98  
% 11.87/1.98  fof(f4,axiom,(
% 11.87/1.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f23,plain,(
% 11.87/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.87/1.98    inference(nnf_transformation,[],[f4])).
% 11.87/1.98  
% 11.87/1.98  fof(f24,plain,(
% 11.87/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.87/1.98    inference(flattening,[],[f23])).
% 11.87/1.98  
% 11.87/1.98  fof(f25,plain,(
% 11.87/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.87/1.98    inference(rectify,[],[f24])).
% 11.87/1.98  
% 11.87/1.98  fof(f26,plain,(
% 11.87/1.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.87/1.98    introduced(choice_axiom,[])).
% 11.87/1.98  
% 11.87/1.98  fof(f27,plain,(
% 11.87/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.87/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 11.87/1.98  
% 11.87/1.98  fof(f44,plain,(
% 11.87/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 11.87/1.98    inference(cnf_transformation,[],[f27])).
% 11.87/1.98  
% 11.87/1.98  fof(f67,plain,(
% 11.87/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.87/1.98    inference(definition_unfolding,[],[f44,f48])).
% 11.87/1.98  
% 11.87/1.98  fof(f71,plain,(
% 11.87/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 11.87/1.98    inference(equality_resolution,[],[f67])).
% 11.87/1.98  
% 11.87/1.98  fof(f62,plain,(
% 11.87/1.98    k2_subset_1(sK3) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)),
% 11.87/1.98    inference(cnf_transformation,[],[f36])).
% 11.87/1.98  
% 11.87/1.98  fof(f39,plain,(
% 11.87/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f22])).
% 11.87/1.98  
% 11.87/1.98  fof(f9,axiom,(
% 11.87/1.98    ! [X0] : k2_subset_1(X0) = X0),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f58,plain,(
% 11.87/1.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.87/1.98    inference(cnf_transformation,[],[f9])).
% 11.87/1.98  
% 11.87/1.98  fof(f42,plain,(
% 11.87/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.87/1.98    inference(cnf_transformation,[],[f27])).
% 11.87/1.98  
% 11.87/1.98  fof(f69,plain,(
% 11.87/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.87/1.98    inference(definition_unfolding,[],[f42,f48])).
% 11.87/1.98  
% 11.87/1.98  fof(f73,plain,(
% 11.87/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.87/1.98    inference(equality_resolution,[],[f69])).
% 11.87/1.98  
% 11.87/1.98  fof(f41,plain,(
% 11.87/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f22])).
% 11.87/1.98  
% 11.87/1.98  fof(f63,plain,(
% 11.87/1.98    k2_subset_1(sK3) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)),
% 11.87/1.98    inference(cnf_transformation,[],[f36])).
% 11.87/1.98  
% 11.87/1.98  fof(f43,plain,(
% 11.87/1.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.87/1.98    inference(cnf_transformation,[],[f27])).
% 11.87/1.98  
% 11.87/1.98  fof(f68,plain,(
% 11.87/1.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.87/1.98    inference(definition_unfolding,[],[f43,f48])).
% 11.87/1.98  
% 11.87/1.98  fof(f72,plain,(
% 11.87/1.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.87/1.98    inference(equality_resolution,[],[f68])).
% 11.87/1.98  
% 11.87/1.98  fof(f1,axiom,(
% 11.87/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f37,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f1])).
% 11.87/1.98  
% 11.87/1.98  fof(f8,axiom,(
% 11.87/1.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f16,plain,(
% 11.87/1.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.87/1.98    inference(ennf_transformation,[],[f8])).
% 11.87/1.98  
% 11.87/1.98  fof(f32,plain,(
% 11.87/1.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.87/1.98    inference(nnf_transformation,[],[f16])).
% 11.87/1.98  
% 11.87/1.98  fof(f54,plain,(
% 11.87/1.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f32])).
% 11.87/1.98  
% 11.87/1.98  fof(f11,axiom,(
% 11.87/1.98    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f60,plain,(
% 11.87/1.98    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.87/1.98    inference(cnf_transformation,[],[f11])).
% 11.87/1.98  
% 11.87/1.98  fof(f7,axiom,(
% 11.87/1.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f28,plain,(
% 11.87/1.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.87/1.98    inference(nnf_transformation,[],[f7])).
% 11.87/1.98  
% 11.87/1.98  fof(f29,plain,(
% 11.87/1.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.87/1.98    inference(rectify,[],[f28])).
% 11.87/1.98  
% 11.87/1.98  fof(f30,plain,(
% 11.87/1.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 11.87/1.98    introduced(choice_axiom,[])).
% 11.87/1.98  
% 11.87/1.98  fof(f31,plain,(
% 11.87/1.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.87/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 11.87/1.98  
% 11.87/1.98  fof(f50,plain,(
% 11.87/1.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.87/1.98    inference(cnf_transformation,[],[f31])).
% 11.87/1.98  
% 11.87/1.98  fof(f75,plain,(
% 11.87/1.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.87/1.98    inference(equality_resolution,[],[f50])).
% 11.87/1.98  
% 11.87/1.98  fof(f6,axiom,(
% 11.87/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f15,plain,(
% 11.87/1.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.87/1.98    inference(ennf_transformation,[],[f6])).
% 11.87/1.98  
% 11.87/1.98  fof(f49,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f15])).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1287,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_47443,plain,
% 11.87/1.98      ( k3_xboole_0(sK3,X0) != X1
% 11.87/1.98      | sK4 != X1
% 11.87/1.98      | sK4 = k3_xboole_0(sK3,X0) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1287]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_47444,plain,
% 11.87/1.98      ( k3_xboole_0(sK3,sK4) != sK4
% 11.87/1.98      | sK4 = k3_xboole_0(sK3,sK4)
% 11.87/1.98      | sK4 != sK4 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_47443]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_3,plain,
% 11.87/1.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.87/1.98      inference(cnf_transformation,[],[f40]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1763,plain,
% 11.87/1.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.87/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_21,plain,
% 11.87/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.87/1.98      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 11.87/1.98      inference(cnf_transformation,[],[f70]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_25,negated_conjecture,
% 11.87/1.98      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 11.87/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_356,plain,
% 11.87/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 11.87/1.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 11.87/1.98      | sK4 != X1 ),
% 11.87/1.98      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_357,plain,
% 11.87/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
% 11.87/1.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 11.87/1.98      inference(unflattening,[status(thm)],[c_356]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1824,plain,
% 11.87/1.98      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
% 11.87/1.98      inference(equality_resolution,[status(thm)],[c_357]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_8,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,X1)
% 11.87/1.98      | r2_hidden(X0,X2)
% 11.87/1.98      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 11.87/1.98      inference(cnf_transformation,[],[f71]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1758,plain,
% 11.87/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.87/1.98      | r2_hidden(X0,X2) = iProver_top
% 11.87/1.98      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_3074,plain,
% 11.87/1.98      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
% 11.87/1.98      | r2_hidden(X0,sK4) = iProver_top
% 11.87/1.98      | r2_hidden(X0,sK3) != iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1824,c_1758]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1290,plain,
% 11.87/1.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.87/1.98      theory(equality) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1286,plain,( X0 = X0 ),theory(equality) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_3120,plain,
% 11.87/1.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.87/1.98      inference(resolution,[status(thm)],[c_1290,c_1286]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_24,negated_conjecture,
% 11.87/1.98      ( r1_tarski(k3_subset_1(sK3,sK4),sK4) | k2_subset_1(sK3) = sK4 ),
% 11.87/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_6120,plain,
% 11.87/1.98      ( r1_tarski(k3_subset_1(sK3,sK4),sK4)
% 11.87/1.98      | r1_tarski(k2_subset_1(sK3),X0)
% 11.87/1.98      | ~ r1_tarski(sK4,X0) ),
% 11.87/1.98      inference(resolution,[status(thm)],[c_3120,c_24]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.87/1.98      inference(cnf_transformation,[],[f39]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_6773,plain,
% 11.87/1.98      ( r2_hidden(X0,X1)
% 11.87/1.98      | ~ r2_hidden(X0,k2_subset_1(sK3))
% 11.87/1.98      | r1_tarski(k3_subset_1(sK3,sK4),sK4)
% 11.87/1.98      | ~ r1_tarski(sK4,X1) ),
% 11.87/1.98      inference(resolution,[status(thm)],[c_6120,c_4]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1301,plain,
% 11.87/1.98      ( sK4 = sK4 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1286]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1292,plain,
% 11.87/1.98      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 11.87/1.98      theory(equality) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1835,plain,
% 11.87/1.98      ( X0 != sK3 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1292]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1836,plain,
% 11.87/1.98      ( k1_zfmisc_1(sK4) = k1_zfmisc_1(sK3) | sK4 != sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1835]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_20,plain,
% 11.87/1.98      ( k2_subset_1(X0) = X0 ),
% 11.87/1.98      inference(cnf_transformation,[],[f58]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2101,plain,
% 11.87/1.98      ( k2_subset_1(sK3) = sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_20]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2409,plain,
% 11.87/1.98      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1287]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2767,plain,
% 11.87/1.98      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_2409]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2769,plain,
% 11.87/1.98      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_2767]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2768,plain,
% 11.87/1.98      ( sK3 = sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1286]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1879,plain,
% 11.87/1.98      ( ~ r1_tarski(X0,X1)
% 11.87/1.98      | r1_tarski(k3_subset_1(sK3,sK4),sK4)
% 11.87/1.98      | k3_subset_1(sK3,sK4) != X0
% 11.87/1.98      | sK4 != X1 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1290]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4313,plain,
% 11.87/1.98      ( ~ r1_tarski(k3_subset_1(X0,X1),X2)
% 11.87/1.98      | r1_tarski(k3_subset_1(sK3,sK4),sK4)
% 11.87/1.98      | k3_subset_1(sK3,sK4) != k3_subset_1(X0,X1)
% 11.87/1.98      | sK4 != X2 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1879]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4316,plain,
% 11.87/1.98      ( ~ r1_tarski(k3_subset_1(sK4,sK4),sK4)
% 11.87/1.98      | r1_tarski(k3_subset_1(sK3,sK4),sK4)
% 11.87/1.98      | k3_subset_1(sK3,sK4) != k3_subset_1(sK4,sK4)
% 11.87/1.98      | sK4 != sK4 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_4313]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1294,plain,
% 11.87/1.98      ( X0 != X1 | X2 != X3 | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
% 11.87/1.98      theory(equality) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4314,plain,
% 11.87/1.98      ( k3_subset_1(sK3,sK4) = k3_subset_1(X0,X1)
% 11.87/1.98      | sK4 != X1
% 11.87/1.98      | sK3 != X0 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1294]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4319,plain,
% 11.87/1.98      ( k3_subset_1(sK3,sK4) = k3_subset_1(sK4,sK4)
% 11.87/1.98      | sK4 != sK4
% 11.87/1.98      | sK3 != sK4 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_4314]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4868,plain,
% 11.87/1.98      ( k2_subset_1(sK3) != sK3 | sK3 = k2_subset_1(sK3) | sK3 != sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_2767]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2401,plain,
% 11.87/1.98      ( sK4 != X0 | sK4 = sK3 | sK3 != X0 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1287]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4977,plain,
% 11.87/1.98      ( sK4 != k2_subset_1(sK3) | sK4 = sK3 | sK3 != k2_subset_1(sK3) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_2401]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_10,plain,
% 11.87/1.98      ( r2_hidden(X0,X1)
% 11.87/1.98      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 11.87/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1756,plain,
% 11.87/1.98      ( r2_hidden(X0,X1) = iProver_top
% 11.87/1.98      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2351,plain,
% 11.87/1.98      ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
% 11.87/1.98      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1763,c_1756]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2,plain,
% 11.87/1.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.87/1.98      inference(cnf_transformation,[],[f41]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1764,plain,
% 11.87/1.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.87/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_5945,plain,
% 11.87/1.98      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_2351,c_1764]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_5985,plain,
% 11.87/1.98      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.87/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_5945]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_5987,plain,
% 11.87/1.98      ( r1_tarski(k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)),sK4) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_5985]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2562,plain,
% 11.87/1.98      ( X0 != X1 | X1 = X0 ),
% 11.87/1.98      inference(resolution,[status(thm)],[c_1287,c_1286]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_6034,plain,
% 11.87/1.98      ( r1_tarski(k3_subset_1(sK3,sK4),sK4) | sK4 = k2_subset_1(sK3) ),
% 11.87/1.98      inference(resolution,[status(thm)],[c_2562,c_24]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_6041,plain,
% 11.87/1.98      ( k3_subset_1(X0,sK4) = k5_xboole_0(X0,k3_xboole_0(X0,sK4))
% 11.87/1.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 11.87/1.98      inference(resolution,[status(thm)],[c_2562,c_357]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_11984,plain,
% 11.87/1.98      ( r1_tarski(k3_subset_1(X0,sK4),X1)
% 11.87/1.98      | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,sK4)),X1)
% 11.87/1.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 11.87/1.98      inference(resolution,[status(thm)],[c_6041,c_3120]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_11998,plain,
% 11.87/1.98      ( r1_tarski(k3_subset_1(sK4,sK4),sK4)
% 11.87/1.98      | ~ r1_tarski(k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)),sK4)
% 11.87/1.98      | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK3) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_11984]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_12011,plain,
% 11.87/1.98      ( r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
% 11.87/1.98      inference(global_propositional_subsumption,
% 11.87/1.98                [status(thm)],
% 11.87/1.98                [c_6773,c_1301,c_1836,c_2101,c_2769,c_2768,c_4316,c_4319,
% 11.87/1.98                 c_4868,c_4977,c_5987,c_6034,c_11998]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_12025,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,k3_subset_1(sK3,sK4)) | r2_hidden(X0,sK4) ),
% 11.87/1.98      inference(resolution,[status(thm)],[c_12011,c_4]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_23,negated_conjecture,
% 11.87/1.98      ( ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) | k2_subset_1(sK3) != sK4 ),
% 11.87/1.98      inference(cnf_transformation,[],[f63]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_190,plain,
% 11.87/1.98      ( r1_tarski(k3_subset_1(sK3,sK4),sK4) | k2_subset_1(sK3) = sK4 ),
% 11.87/1.98      inference(prop_impl,[status(thm)],[c_24]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_610,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,X1)
% 11.87/1.98      | r2_hidden(X0,X2)
% 11.87/1.98      | k3_subset_1(sK3,sK4) != X1
% 11.87/1.98      | k2_subset_1(sK3) = sK4
% 11.87/1.98      | sK4 != X2 ),
% 11.87/1.98      inference(resolution_lifted,[status(thm)],[c_4,c_190]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_611,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,k3_subset_1(sK3,sK4))
% 11.87/1.98      | r2_hidden(X0,sK4)
% 11.87/1.98      | k2_subset_1(sK3) = sK4 ),
% 11.87/1.98      inference(unflattening,[status(thm)],[c_610]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_9,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,X1)
% 11.87/1.98      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 11.87/1.98      inference(cnf_transformation,[],[f72]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1757,plain,
% 11.87/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.87/1.98      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_3076,plain,
% 11.87/1.98      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
% 11.87/1.98      | r2_hidden(X0,sK4) != iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1824,c_1757]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_3083,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,k3_subset_1(sK3,sK4)) | ~ r2_hidden(X0,sK4) ),
% 11.87/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_3076]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_19481,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,k3_subset_1(sK3,sK4)) ),
% 11.87/1.98      inference(global_propositional_subsumption,
% 11.87/1.98                [status(thm)],
% 11.87/1.98                [c_12025,c_23,c_611,c_1301,c_1836,c_2101,c_2769,c_2768,
% 11.87/1.98                 c_3083,c_4316,c_4319,c_4868,c_4977,c_5987,c_6034,
% 11.87/1.98                 c_11998]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_19483,plain,
% 11.87/1.98      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_19481]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_32430,plain,
% 11.87/1.98      ( r2_hidden(X0,sK4) = iProver_top
% 11.87/1.98      | r2_hidden(X0,sK3) != iProver_top ),
% 11.87/1.98      inference(global_propositional_subsumption,
% 11.87/1.98                [status(thm)],
% 11.87/1.98                [c_3074,c_19483]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_32436,plain,
% 11.87/1.98      ( r2_hidden(sK0(sK3,X0),sK4) = iProver_top
% 11.87/1.98      | r1_tarski(sK3,X0) = iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1763,c_32430]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_32462,plain,
% 11.87/1.98      ( r2_hidden(sK0(sK3,X0),sK4) | r1_tarski(sK3,X0) ),
% 11.87/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_32436]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_32464,plain,
% 11.87/1.98      ( r2_hidden(sK0(sK3,sK4),sK4) | r1_tarski(sK3,sK4) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_32462]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1941,plain,
% 11.87/1.98      ( k2_subset_1(sK3) != X0 | k2_subset_1(sK3) = sK4 | sK4 != X0 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1287]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_17754,plain,
% 11.87/1.98      ( k2_subset_1(sK3) != k3_xboole_0(sK3,X0)
% 11.87/1.98      | k2_subset_1(sK3) = sK4
% 11.87/1.98      | sK4 != k3_xboole_0(sK3,X0) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1941]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_17755,plain,
% 11.87/1.98      ( k2_subset_1(sK3) != k3_xboole_0(sK3,sK4)
% 11.87/1.98      | k2_subset_1(sK3) = sK4
% 11.87/1.98      | sK4 != k3_xboole_0(sK3,sK4) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_17754]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4690,plain,
% 11.87/1.98      ( ~ r2_hidden(sK0(sK3,X0),X0) | r1_tarski(sK3,X0) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4702,plain,
% 11.87/1.98      ( ~ r2_hidden(sK0(sK3,sK4),sK4) | r1_tarski(sK3,sK4) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_4690]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_0,plain,
% 11.87/1.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.87/1.98      inference(cnf_transformation,[],[f37]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_19,plain,
% 11.87/1.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.87/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_343,plain,
% 11.87/1.98      ( r2_hidden(X0,X1)
% 11.87/1.98      | v1_xboole_0(X1)
% 11.87/1.98      | k1_zfmisc_1(sK3) != X1
% 11.87/1.98      | sK4 != X0 ),
% 11.87/1.98      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_344,plain,
% 11.87/1.98      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 11.87/1.98      inference(unflattening,[status(thm)],[c_343]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_22,plain,
% 11.87/1.98      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.87/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_350,plain,
% 11.87/1.98      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
% 11.87/1.98      inference(forward_subsumption_resolution,
% 11.87/1.98                [status(thm)],
% 11.87/1.98                [c_344,c_22]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1748,plain,
% 11.87/1.98      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_15,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.87/1.98      inference(cnf_transformation,[],[f75]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1751,plain,
% 11.87/1.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.87/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2131,plain,
% 11.87/1.98      ( r1_tarski(sK4,sK3) = iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1748,c_1751]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_11,plain,
% 11.87/1.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.87/1.98      inference(cnf_transformation,[],[f49]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1755,plain,
% 11.87/1.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_3344,plain,
% 11.87/1.98      ( k3_xboole_0(sK4,sK3) = sK4 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_2131,c_1755]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_3519,plain,
% 11.87/1.98      ( k3_xboole_0(sK3,sK4) = sK4 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_0,c_3344]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2655,plain,
% 11.87/1.98      ( ~ r1_tarski(sK3,X0) | k3_xboole_0(sK3,X0) = sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_11]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2658,plain,
% 11.87/1.98      ( ~ r1_tarski(sK3,sK4) | k3_xboole_0(sK3,sK4) = sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_2655]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2104,plain,
% 11.87/1.98      ( X0 != X1 | k2_subset_1(sK3) != X1 | k2_subset_1(sK3) = X0 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_1287]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2417,plain,
% 11.87/1.98      ( X0 != sK3 | k2_subset_1(sK3) = X0 | k2_subset_1(sK3) != sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_2104]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2654,plain,
% 11.87/1.98      ( k3_xboole_0(sK3,X0) != sK3
% 11.87/1.98      | k2_subset_1(sK3) = k3_xboole_0(sK3,X0)
% 11.87/1.98      | k2_subset_1(sK3) != sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_2417]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2656,plain,
% 11.87/1.98      ( k3_xboole_0(sK3,sK4) != sK3
% 11.87/1.98      | k2_subset_1(sK3) = k3_xboole_0(sK3,sK4)
% 11.87/1.98      | k2_subset_1(sK3) != sK3 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_2654]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(contradiction,plain,
% 11.87/1.98      ( $false ),
% 11.87/1.98      inference(minisat,
% 11.87/1.98                [status(thm)],
% 11.87/1.98                [c_47444,c_32464,c_17755,c_12011,c_4702,c_3519,c_2658,
% 11.87/1.98                 c_2656,c_2101,c_1301,c_23]) ).
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  ------                               Statistics
% 11.87/1.98  
% 11.87/1.98  ------ Selected
% 11.87/1.98  
% 11.87/1.98  total_time:                             1.275
% 11.87/1.98  
%------------------------------------------------------------------------------
