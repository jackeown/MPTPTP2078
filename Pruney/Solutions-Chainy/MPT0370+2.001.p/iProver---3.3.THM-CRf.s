%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:02 EST 2020

% Result     : Theorem 6.94s
% Output     : CNFRefutation 6.94s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 267 expanded)
%              Number of clauses        :   84 (  90 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  547 (1294 expanded)
%              Number of equality atoms :  118 ( 193 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
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

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f52])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> ~ r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f63,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK7) != X1
        & ! [X3] :
            ( ( ( r2_hidden(X3,X1)
                | r2_hidden(X3,sK7) )
              & ( ~ r2_hidden(X3,sK7)
                | ~ r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | r2_hidden(X3,X2) )
                  & ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK5,X2) != sK6
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK6)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK6) ) )
              | ~ m1_subset_1(X3,sK5) )
          & m1_subset_1(X2,k1_zfmisc_1(sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( k3_subset_1(sK5,sK7) != sK6
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK6)
            | r2_hidden(X3,sK7) )
          & ( ~ r2_hidden(X3,sK7)
            | ~ r2_hidden(X3,sK6) ) )
        | ~ m1_subset_1(X3,sK5) )
    & m1_subset_1(sK7,k1_zfmisc_1(sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f63,f65,f64])).

fof(f107,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f66])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f110,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK6)
      | r2_hidden(X3,sK7)
      | ~ m1_subset_1(X3,sK5) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f109,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK7)
      | ~ r2_hidden(X3,sK6)
      | ~ m1_subset_1(X3,sK5) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f59])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X2)
          | ~ r2_hidden(sK4(X0,X1,X2),X1) )
        & ( r2_hidden(sK4(X0,X1,X2),X2)
          | r2_hidden(sK4(X0,X1,X2),X1) )
        & m1_subset_1(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK4(X0,X1,X2),X2)
              | ~ r2_hidden(sK4(X0,X1,X2),X1) )
            & ( r2_hidden(sK4(X0,X1,X2),X2)
              | r2_hidden(sK4(X0,X1,X2),X1) )
            & m1_subset_1(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f111,plain,(
    k3_subset_1(sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f66])).

fof(f108,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_xboole_0(X0,k3_subset_1(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_4575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
    | r1_xboole_0(X0,k3_subset_1(sK5,sK7))
    | ~ r1_tarski(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_19697,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
    | r1_xboole_0(sK7,k3_subset_1(sK5,sK7))
    | ~ r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_4575])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4153,plain,
    ( ~ r1_tarski(sK6,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X1,sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6696,plain,
    ( ~ r1_tarski(sK6,X0)
    | r2_hidden(sK3(X1,sK7),X0)
    | ~ r2_hidden(sK3(X1,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_4153])).

cnf(c_14056,plain,
    ( ~ r1_tarski(sK6,X0)
    | r2_hidden(sK3(sK6,sK7),X0)
    | ~ r2_hidden(sK3(sK6,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_6696])).

cnf(c_14058,plain,
    ( r1_tarski(sK6,X0) != iProver_top
    | r2_hidden(sK3(sK6,sK7),X0) = iProver_top
    | r2_hidden(sK3(sK6,sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14056])).

cnf(c_14060,plain,
    ( r1_tarski(sK6,sK5) != iProver_top
    | r2_hidden(sK3(sK6,sK7),sK6) != iProver_top
    | r2_hidden(sK3(sK6,sK7),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14058])).

cnf(c_6690,plain,
    ( ~ r1_tarski(sK6,X0)
    | r2_hidden(sK4(X1,k3_subset_1(sK5,sK7),sK6),X0)
    | ~ r2_hidden(sK4(X1,k3_subset_1(sK5,sK7),sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_4153])).

cnf(c_13907,plain,
    ( ~ r1_tarski(sK6,k3_subset_1(sK5,sK7))
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7))
    | ~ r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_6690])).

cnf(c_13908,plain,
    ( r1_tarski(sK6,k3_subset_1(sK5,sK7)) != iProver_top
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13907])).

cnf(c_13910,plain,
    ( r1_tarski(sK6,k3_subset_1(sK5,sK7)) != iProver_top
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13908])).

cnf(c_15,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_6207,plain,
    ( r1_xboole_0(X0,sK7)
    | r2_hidden(sK3(X0,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_11653,plain,
    ( r1_xboole_0(sK6,sK7)
    | r2_hidden(sK3(sK6,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_6207])).

cnf(c_11655,plain,
    ( r1_xboole_0(sK6,sK7) = iProver_top
    | r2_hidden(sK3(sK6,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11653])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_10618,plain,
    ( ~ r1_xboole_0(sK7,k3_subset_1(sK5,sK7))
    | k3_xboole_0(sK7,k3_subset_1(sK5,sK7)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1770,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1733,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1744,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5573,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_1744])).

cnf(c_5751,plain,
    ( r1_tarski(sK6,X0) = iProver_top
    | r2_hidden(sK1(sK6,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_5573])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1771,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10542,plain,
    ( r1_tarski(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5751,c_1771])).

cnf(c_29,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_1])).

cnf(c_249,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_2024,plain,
    ( m1_subset_1(sK3(X0,sK7),sK5)
    | ~ r2_hidden(sK3(X0,sK7),sK5) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_7268,plain,
    ( m1_subset_1(sK3(sK6,sK7),sK5)
    | ~ r2_hidden(sK3(sK6,sK7),sK5) ),
    inference(instantiation,[status(thm)],[c_2024])).

cnf(c_7269,plain,
    ( m1_subset_1(sK3(sK6,sK7),sK5) = iProver_top
    | r2_hidden(sK3(sK6,sK7),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7268])).

cnf(c_41,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK6)
    | r2_hidden(X0,sK7) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_6441,plain,
    ( ~ m1_subset_1(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK5)
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK6)
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_6442,plain,
    ( m1_subset_1(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK5) != iProver_top
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK6) = iProver_top
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6441])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3474,plain,
    ( ~ r1_xboole_0(X0,k3_subset_1(sK5,sK7))
    | ~ r2_hidden(sK4(X1,k3_subset_1(sK5,sK7),sK6),X0)
    | ~ r2_hidden(sK4(X1,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_5716,plain,
    ( ~ r1_xboole_0(sK7,k3_subset_1(sK5,sK7))
    | ~ r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7))
    | ~ r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_3474])).

cnf(c_5719,plain,
    ( r1_xboole_0(sK7,k3_subset_1(sK5,sK7)) != iProver_top
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) != iProver_top
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5716])).

cnf(c_5721,plain,
    ( r1_xboole_0(sK7,k3_subset_1(sK5,sK7)) != iProver_top
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) != iProver_top
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5719])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3114,plain,
    ( r1_xboole_0(sK7,X0)
    | k3_xboole_0(sK7,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5715,plain,
    ( r1_xboole_0(sK7,k3_subset_1(sK5,sK7))
    | k3_xboole_0(sK7,k3_subset_1(sK5,sK7)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3114])).

cnf(c_5717,plain,
    ( k3_xboole_0(sK7,k3_subset_1(sK5,sK7)) != k1_xboole_0
    | r1_xboole_0(sK7,k3_subset_1(sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5715])).

cnf(c_16,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2716,plain,
    ( r1_xboole_0(sK6,X0)
    | r2_hidden(sK3(sK6,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_5620,plain,
    ( r1_xboole_0(sK6,sK7)
    | r2_hidden(sK3(sK6,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_2716])).

cnf(c_5621,plain,
    ( r1_xboole_0(sK6,sK7) = iProver_top
    | r2_hidden(sK3(sK6,sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5620])).

cnf(c_2918,plain,
    ( r1_tarski(X0,sK7)
    | r2_hidden(sK1(X0,sK7),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4171,plain,
    ( r1_tarski(sK7,sK7)
    | r2_hidden(sK1(sK7,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_2918])).

cnf(c_2917,plain,
    ( r1_tarski(X0,sK7)
    | ~ r2_hidden(sK1(X0,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4172,plain,
    ( r1_tarski(sK7,sK7)
    | ~ r2_hidden(sK1(sK7,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_2917])).

cnf(c_42,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X0,sK7) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2006,plain,
    ( ~ m1_subset_1(sK3(sK6,X0),sK5)
    | ~ r2_hidden(sK3(sK6,X0),sK6)
    | ~ r2_hidden(sK3(sK6,X0),sK7) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_3682,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
    | ~ r2_hidden(sK3(sK6,sK7),sK6)
    | ~ r2_hidden(sK3(sK6,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_3685,plain,
    ( m1_subset_1(sK3(sK6,sK7),sK5) != iProver_top
    | r2_hidden(sK3(sK6,sK7),sK6) != iProver_top
    | r2_hidden(sK3(sK6,sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3682])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2410,plain,
    ( m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2411,plain,
    ( m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2410])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X0,X2)
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2388,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
    | ~ r1_xboole_0(sK6,sK7)
    | r1_tarski(sK6,k3_subset_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_2389,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top
    | r1_xboole_0(sK6,sK7) != iProver_top
    | r1_tarski(sK6,k3_subset_1(sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2388])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK4(X1,X0,X2),X2)
    | ~ r2_hidden(sK4(X1,X0,X2),X0)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1820,plain,
    ( ~ m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7))
    | ~ r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6)
    | k3_subset_1(sK5,sK7) = sK6 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_1831,plain,
    ( k3_subset_1(sK5,sK7) = sK6
    | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) != iProver_top
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1820])).

cnf(c_1833,plain,
    ( k3_subset_1(sK5,sK7) = sK6
    | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) != iProver_top
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK4(X1,X0,X2),X2)
    | r2_hidden(sK4(X1,X0,X2),X0)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1821,plain,
    ( ~ m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7))
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6)
    | k3_subset_1(sK5,sK7) = sK6 ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_1827,plain,
    ( k3_subset_1(sK5,sK7) = sK6
    | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1821])).

cnf(c_1829,plain,
    ( k3_subset_1(sK5,sK7) = sK6
    | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK4(X1,X0,X2),X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1822,plain,
    ( m1_subset_1(sK4(X0,k3_subset_1(sK5,sK7),sK6),X0)
    | ~ m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | k3_subset_1(sK5,sK7) = sK6 ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_1823,plain,
    ( k3_subset_1(sK5,sK7) = sK6
    | m1_subset_1(sK4(X0,k3_subset_1(sK5,sK7),sK6),X0) = iProver_top
    | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1822])).

cnf(c_1825,plain,
    ( k3_subset_1(sK5,sK7) = sK6
    | m1_subset_1(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK5) = iProver_top
    | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_40,negated_conjecture,
    ( k3_subset_1(sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_46,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_45,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19697,c_14060,c_13910,c_11655,c_10618,c_10542,c_7269,c_6442,c_5721,c_5717,c_5621,c_4171,c_4172,c_3685,c_2411,c_2389,c_1833,c_1829,c_1825,c_40,c_46,c_43,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  % Running in FOF mode
% 6.94/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/1.49  
% 6.94/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.94/1.49  
% 6.94/1.49  ------  iProver source info
% 6.94/1.49  
% 6.94/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.94/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.94/1.49  git: non_committed_changes: false
% 6.94/1.49  git: last_make_outside_of_git: false
% 6.94/1.49  
% 6.94/1.49  ------ 
% 6.94/1.49  
% 6.94/1.49  ------ Input Options
% 6.94/1.49  
% 6.94/1.49  --out_options                           all
% 6.94/1.49  --tptp_safe_out                         true
% 6.94/1.49  --problem_path                          ""
% 6.94/1.49  --include_path                          ""
% 6.94/1.49  --clausifier                            res/vclausify_rel
% 6.94/1.49  --clausifier_options                    ""
% 6.94/1.49  --stdin                                 false
% 6.94/1.49  --stats_out                             all
% 6.94/1.49  
% 6.94/1.49  ------ General Options
% 6.94/1.49  
% 6.94/1.49  --fof                                   false
% 6.94/1.49  --time_out_real                         305.
% 6.94/1.49  --time_out_virtual                      -1.
% 6.94/1.49  --symbol_type_check                     false
% 6.94/1.49  --clausify_out                          false
% 6.94/1.49  --sig_cnt_out                           false
% 6.94/1.49  --trig_cnt_out                          false
% 6.94/1.49  --trig_cnt_out_tolerance                1.
% 6.94/1.49  --trig_cnt_out_sk_spl                   false
% 6.94/1.49  --abstr_cl_out                          false
% 6.94/1.49  
% 6.94/1.49  ------ Global Options
% 6.94/1.49  
% 6.94/1.49  --schedule                              default
% 6.94/1.49  --add_important_lit                     false
% 6.94/1.49  --prop_solver_per_cl                    1000
% 6.94/1.49  --min_unsat_core                        false
% 6.94/1.49  --soft_assumptions                      false
% 6.94/1.49  --soft_lemma_size                       3
% 6.94/1.49  --prop_impl_unit_size                   0
% 6.94/1.49  --prop_impl_unit                        []
% 6.94/1.49  --share_sel_clauses                     true
% 6.94/1.49  --reset_solvers                         false
% 6.94/1.49  --bc_imp_inh                            [conj_cone]
% 6.94/1.49  --conj_cone_tolerance                   3.
% 6.94/1.49  --extra_neg_conj                        none
% 6.94/1.49  --large_theory_mode                     true
% 6.94/1.49  --prolific_symb_bound                   200
% 6.94/1.49  --lt_threshold                          2000
% 6.94/1.49  --clause_weak_htbl                      true
% 6.94/1.49  --gc_record_bc_elim                     false
% 6.94/1.49  
% 6.94/1.49  ------ Preprocessing Options
% 6.94/1.49  
% 6.94/1.49  --preprocessing_flag                    true
% 6.94/1.49  --time_out_prep_mult                    0.1
% 6.94/1.49  --splitting_mode                        input
% 6.94/1.49  --splitting_grd                         true
% 6.94/1.49  --splitting_cvd                         false
% 6.94/1.49  --splitting_cvd_svl                     false
% 6.94/1.49  --splitting_nvd                         32
% 6.94/1.49  --sub_typing                            true
% 6.94/1.49  --prep_gs_sim                           true
% 6.94/1.49  --prep_unflatten                        true
% 6.94/1.49  --prep_res_sim                          true
% 6.94/1.49  --prep_upred                            true
% 6.94/1.49  --prep_sem_filter                       exhaustive
% 6.94/1.49  --prep_sem_filter_out                   false
% 6.94/1.49  --pred_elim                             true
% 6.94/1.49  --res_sim_input                         true
% 6.94/1.49  --eq_ax_congr_red                       true
% 6.94/1.49  --pure_diseq_elim                       true
% 6.94/1.49  --brand_transform                       false
% 6.94/1.49  --non_eq_to_eq                          false
% 6.94/1.49  --prep_def_merge                        true
% 6.94/1.49  --prep_def_merge_prop_impl              false
% 6.94/1.49  --prep_def_merge_mbd                    true
% 6.94/1.49  --prep_def_merge_tr_red                 false
% 6.94/1.49  --prep_def_merge_tr_cl                  false
% 6.94/1.49  --smt_preprocessing                     true
% 6.94/1.49  --smt_ac_axioms                         fast
% 6.94/1.49  --preprocessed_out                      false
% 6.94/1.49  --preprocessed_stats                    false
% 6.94/1.49  
% 6.94/1.49  ------ Abstraction refinement Options
% 6.94/1.49  
% 6.94/1.49  --abstr_ref                             []
% 6.94/1.49  --abstr_ref_prep                        false
% 6.94/1.49  --abstr_ref_until_sat                   false
% 6.94/1.49  --abstr_ref_sig_restrict                funpre
% 6.94/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.94/1.49  --abstr_ref_under                       []
% 6.94/1.49  
% 6.94/1.49  ------ SAT Options
% 6.94/1.49  
% 6.94/1.49  --sat_mode                              false
% 6.94/1.49  --sat_fm_restart_options                ""
% 6.94/1.49  --sat_gr_def                            false
% 6.94/1.49  --sat_epr_types                         true
% 6.94/1.49  --sat_non_cyclic_types                  false
% 6.94/1.49  --sat_finite_models                     false
% 6.94/1.49  --sat_fm_lemmas                         false
% 6.94/1.49  --sat_fm_prep                           false
% 6.94/1.49  --sat_fm_uc_incr                        true
% 6.94/1.49  --sat_out_model                         small
% 6.94/1.49  --sat_out_clauses                       false
% 6.94/1.49  
% 6.94/1.49  ------ QBF Options
% 6.94/1.49  
% 6.94/1.49  --qbf_mode                              false
% 6.94/1.49  --qbf_elim_univ                         false
% 6.94/1.49  --qbf_dom_inst                          none
% 6.94/1.49  --qbf_dom_pre_inst                      false
% 6.94/1.49  --qbf_sk_in                             false
% 6.94/1.49  --qbf_pred_elim                         true
% 6.94/1.49  --qbf_split                             512
% 6.94/1.49  
% 6.94/1.49  ------ BMC1 Options
% 6.94/1.49  
% 6.94/1.49  --bmc1_incremental                      false
% 6.94/1.49  --bmc1_axioms                           reachable_all
% 6.94/1.49  --bmc1_min_bound                        0
% 6.94/1.49  --bmc1_max_bound                        -1
% 6.94/1.49  --bmc1_max_bound_default                -1
% 6.94/1.49  --bmc1_symbol_reachability              true
% 6.94/1.49  --bmc1_property_lemmas                  false
% 6.94/1.49  --bmc1_k_induction                      false
% 6.94/1.49  --bmc1_non_equiv_states                 false
% 6.94/1.49  --bmc1_deadlock                         false
% 6.94/1.49  --bmc1_ucm                              false
% 6.94/1.49  --bmc1_add_unsat_core                   none
% 6.94/1.49  --bmc1_unsat_core_children              false
% 6.94/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.94/1.49  --bmc1_out_stat                         full
% 6.94/1.49  --bmc1_ground_init                      false
% 6.94/1.49  --bmc1_pre_inst_next_state              false
% 6.94/1.49  --bmc1_pre_inst_state                   false
% 6.94/1.49  --bmc1_pre_inst_reach_state             false
% 6.94/1.49  --bmc1_out_unsat_core                   false
% 6.94/1.49  --bmc1_aig_witness_out                  false
% 6.94/1.49  --bmc1_verbose                          false
% 6.94/1.49  --bmc1_dump_clauses_tptp                false
% 6.94/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.94/1.49  --bmc1_dump_file                        -
% 6.94/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.94/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.94/1.49  --bmc1_ucm_extend_mode                  1
% 6.94/1.49  --bmc1_ucm_init_mode                    2
% 6.94/1.49  --bmc1_ucm_cone_mode                    none
% 6.94/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.94/1.49  --bmc1_ucm_relax_model                  4
% 6.94/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.94/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.94/1.49  --bmc1_ucm_layered_model                none
% 6.94/1.49  --bmc1_ucm_max_lemma_size               10
% 6.94/1.49  
% 6.94/1.49  ------ AIG Options
% 6.94/1.49  
% 6.94/1.49  --aig_mode                              false
% 6.94/1.49  
% 6.94/1.49  ------ Instantiation Options
% 6.94/1.49  
% 6.94/1.49  --instantiation_flag                    true
% 6.94/1.49  --inst_sos_flag                         true
% 6.94/1.49  --inst_sos_phase                        true
% 6.94/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.94/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.94/1.49  --inst_lit_sel_side                     num_symb
% 6.94/1.49  --inst_solver_per_active                1400
% 6.94/1.49  --inst_solver_calls_frac                1.
% 6.94/1.49  --inst_passive_queue_type               priority_queues
% 6.94/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.94/1.49  --inst_passive_queues_freq              [25;2]
% 6.94/1.49  --inst_dismatching                      true
% 6.94/1.49  --inst_eager_unprocessed_to_passive     true
% 6.94/1.49  --inst_prop_sim_given                   true
% 6.94/1.49  --inst_prop_sim_new                     false
% 6.94/1.49  --inst_subs_new                         false
% 6.94/1.49  --inst_eq_res_simp                      false
% 6.94/1.49  --inst_subs_given                       false
% 6.94/1.49  --inst_orphan_elimination               true
% 6.94/1.49  --inst_learning_loop_flag               true
% 6.94/1.49  --inst_learning_start                   3000
% 6.94/1.49  --inst_learning_factor                  2
% 6.94/1.49  --inst_start_prop_sim_after_learn       3
% 6.94/1.49  --inst_sel_renew                        solver
% 6.94/1.49  --inst_lit_activity_flag                true
% 6.94/1.49  --inst_restr_to_given                   false
% 6.94/1.49  --inst_activity_threshold               500
% 6.94/1.49  --inst_out_proof                        true
% 6.94/1.49  
% 6.94/1.49  ------ Resolution Options
% 6.94/1.49  
% 6.94/1.49  --resolution_flag                       true
% 6.94/1.49  --res_lit_sel                           adaptive
% 6.94/1.49  --res_lit_sel_side                      none
% 6.94/1.49  --res_ordering                          kbo
% 6.94/1.49  --res_to_prop_solver                    active
% 6.94/1.49  --res_prop_simpl_new                    false
% 6.94/1.49  --res_prop_simpl_given                  true
% 6.94/1.49  --res_passive_queue_type                priority_queues
% 6.94/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.94/1.49  --res_passive_queues_freq               [15;5]
% 6.94/1.49  --res_forward_subs                      full
% 6.94/1.49  --res_backward_subs                     full
% 6.94/1.49  --res_forward_subs_resolution           true
% 6.94/1.49  --res_backward_subs_resolution          true
% 6.94/1.49  --res_orphan_elimination                true
% 6.94/1.49  --res_time_limit                        2.
% 6.94/1.49  --res_out_proof                         true
% 6.94/1.49  
% 6.94/1.49  ------ Superposition Options
% 6.94/1.49  
% 6.94/1.49  --superposition_flag                    true
% 6.94/1.49  --sup_passive_queue_type                priority_queues
% 6.94/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.94/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.94/1.49  --demod_completeness_check              fast
% 6.94/1.49  --demod_use_ground                      true
% 6.94/1.49  --sup_to_prop_solver                    passive
% 6.94/1.49  --sup_prop_simpl_new                    true
% 6.94/1.49  --sup_prop_simpl_given                  true
% 6.94/1.49  --sup_fun_splitting                     true
% 6.94/1.49  --sup_smt_interval                      50000
% 6.94/1.49  
% 6.94/1.49  ------ Superposition Simplification Setup
% 6.94/1.49  
% 6.94/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.94/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.94/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.94/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.94/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.94/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.94/1.49  --sup_immed_triv                        [TrivRules]
% 6.94/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.94/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.94/1.49  --sup_immed_bw_main                     []
% 6.94/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.94/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.94/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.94/1.49  --sup_input_bw                          []
% 6.94/1.49  
% 6.94/1.49  ------ Combination Options
% 6.94/1.49  
% 6.94/1.49  --comb_res_mult                         3
% 6.94/1.49  --comb_sup_mult                         2
% 6.94/1.49  --comb_inst_mult                        10
% 6.94/1.49  
% 6.94/1.49  ------ Debug Options
% 6.94/1.49  
% 6.94/1.49  --dbg_backtrace                         false
% 6.94/1.49  --dbg_dump_prop_clauses                 false
% 6.94/1.49  --dbg_dump_prop_clauses_file            -
% 6.94/1.49  --dbg_out_stat                          false
% 6.94/1.49  ------ Parsing...
% 6.94/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.94/1.49  
% 6.94/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.94/1.49  
% 6.94/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.94/1.49  
% 6.94/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.94/1.49  ------ Proving...
% 6.94/1.49  ------ Problem Properties 
% 6.94/1.49  
% 6.94/1.49  
% 6.94/1.49  clauses                                 44
% 6.94/1.49  conjectures                             5
% 6.94/1.49  EPR                                     13
% 6.94/1.49  Horn                                    34
% 6.94/1.49  unary                                   6
% 6.94/1.49  binary                                  16
% 6.94/1.49  lits                                    114
% 6.94/1.49  lits eq                                 12
% 6.94/1.49  fd_pure                                 0
% 6.94/1.49  fd_pseudo                               0
% 6.94/1.49  fd_cond                                 0
% 6.94/1.49  fd_pseudo_cond                          7
% 6.94/1.49  AC symbols                              0
% 6.94/1.49  
% 6.94/1.49  ------ Schedule dynamic 5 is on 
% 6.94/1.49  
% 6.94/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.94/1.49  
% 6.94/1.49  
% 6.94/1.49  ------ 
% 6.94/1.49  Current options:
% 6.94/1.49  ------ 
% 6.94/1.49  
% 6.94/1.49  ------ Input Options
% 6.94/1.49  
% 6.94/1.49  --out_options                           all
% 6.94/1.49  --tptp_safe_out                         true
% 6.94/1.49  --problem_path                          ""
% 6.94/1.49  --include_path                          ""
% 6.94/1.49  --clausifier                            res/vclausify_rel
% 6.94/1.49  --clausifier_options                    ""
% 6.94/1.49  --stdin                                 false
% 6.94/1.49  --stats_out                             all
% 6.94/1.49  
% 6.94/1.49  ------ General Options
% 6.94/1.49  
% 6.94/1.49  --fof                                   false
% 6.94/1.49  --time_out_real                         305.
% 6.94/1.49  --time_out_virtual                      -1.
% 6.94/1.49  --symbol_type_check                     false
% 6.94/1.49  --clausify_out                          false
% 6.94/1.49  --sig_cnt_out                           false
% 6.94/1.49  --trig_cnt_out                          false
% 6.94/1.49  --trig_cnt_out_tolerance                1.
% 6.94/1.49  --trig_cnt_out_sk_spl                   false
% 6.94/1.49  --abstr_cl_out                          false
% 6.94/1.49  
% 6.94/1.49  ------ Global Options
% 6.94/1.49  
% 6.94/1.49  --schedule                              default
% 6.94/1.49  --add_important_lit                     false
% 6.94/1.49  --prop_solver_per_cl                    1000
% 6.94/1.49  --min_unsat_core                        false
% 6.94/1.49  --soft_assumptions                      false
% 6.94/1.49  --soft_lemma_size                       3
% 6.94/1.49  --prop_impl_unit_size                   0
% 6.94/1.49  --prop_impl_unit                        []
% 6.94/1.49  --share_sel_clauses                     true
% 6.94/1.49  --reset_solvers                         false
% 6.94/1.49  --bc_imp_inh                            [conj_cone]
% 6.94/1.49  --conj_cone_tolerance                   3.
% 6.94/1.49  --extra_neg_conj                        none
% 6.94/1.49  --large_theory_mode                     true
% 6.94/1.49  --prolific_symb_bound                   200
% 6.94/1.49  --lt_threshold                          2000
% 6.94/1.49  --clause_weak_htbl                      true
% 6.94/1.49  --gc_record_bc_elim                     false
% 6.94/1.49  
% 6.94/1.49  ------ Preprocessing Options
% 6.94/1.49  
% 6.94/1.49  --preprocessing_flag                    true
% 6.94/1.49  --time_out_prep_mult                    0.1
% 6.94/1.49  --splitting_mode                        input
% 6.94/1.49  --splitting_grd                         true
% 6.94/1.49  --splitting_cvd                         false
% 6.94/1.49  --splitting_cvd_svl                     false
% 6.94/1.49  --splitting_nvd                         32
% 6.94/1.49  --sub_typing                            true
% 6.94/1.49  --prep_gs_sim                           true
% 6.94/1.49  --prep_unflatten                        true
% 6.94/1.49  --prep_res_sim                          true
% 6.94/1.49  --prep_upred                            true
% 6.94/1.49  --prep_sem_filter                       exhaustive
% 6.94/1.49  --prep_sem_filter_out                   false
% 6.94/1.49  --pred_elim                             true
% 6.94/1.49  --res_sim_input                         true
% 6.94/1.49  --eq_ax_congr_red                       true
% 6.94/1.49  --pure_diseq_elim                       true
% 6.94/1.49  --brand_transform                       false
% 6.94/1.49  --non_eq_to_eq                          false
% 6.94/1.49  --prep_def_merge                        true
% 6.94/1.49  --prep_def_merge_prop_impl              false
% 6.94/1.49  --prep_def_merge_mbd                    true
% 6.94/1.49  --prep_def_merge_tr_red                 false
% 6.94/1.49  --prep_def_merge_tr_cl                  false
% 6.94/1.49  --smt_preprocessing                     true
% 6.94/1.49  --smt_ac_axioms                         fast
% 6.94/1.49  --preprocessed_out                      false
% 6.94/1.49  --preprocessed_stats                    false
% 6.94/1.49  
% 6.94/1.49  ------ Abstraction refinement Options
% 6.94/1.49  
% 6.94/1.49  --abstr_ref                             []
% 6.94/1.49  --abstr_ref_prep                        false
% 6.94/1.49  --abstr_ref_until_sat                   false
% 6.94/1.49  --abstr_ref_sig_restrict                funpre
% 6.94/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.94/1.49  --abstr_ref_under                       []
% 6.94/1.49  
% 6.94/1.49  ------ SAT Options
% 6.94/1.49  
% 6.94/1.49  --sat_mode                              false
% 6.94/1.49  --sat_fm_restart_options                ""
% 6.94/1.49  --sat_gr_def                            false
% 6.94/1.49  --sat_epr_types                         true
% 6.94/1.49  --sat_non_cyclic_types                  false
% 6.94/1.49  --sat_finite_models                     false
% 6.94/1.49  --sat_fm_lemmas                         false
% 6.94/1.49  --sat_fm_prep                           false
% 6.94/1.49  --sat_fm_uc_incr                        true
% 6.94/1.49  --sat_out_model                         small
% 6.94/1.49  --sat_out_clauses                       false
% 6.94/1.49  
% 6.94/1.49  ------ QBF Options
% 6.94/1.49  
% 6.94/1.49  --qbf_mode                              false
% 6.94/1.49  --qbf_elim_univ                         false
% 6.94/1.49  --qbf_dom_inst                          none
% 6.94/1.49  --qbf_dom_pre_inst                      false
% 6.94/1.49  --qbf_sk_in                             false
% 6.94/1.49  --qbf_pred_elim                         true
% 6.94/1.49  --qbf_split                             512
% 6.94/1.49  
% 6.94/1.49  ------ BMC1 Options
% 6.94/1.49  
% 6.94/1.49  --bmc1_incremental                      false
% 6.94/1.49  --bmc1_axioms                           reachable_all
% 6.94/1.49  --bmc1_min_bound                        0
% 6.94/1.49  --bmc1_max_bound                        -1
% 6.94/1.49  --bmc1_max_bound_default                -1
% 6.94/1.49  --bmc1_symbol_reachability              true
% 6.94/1.49  --bmc1_property_lemmas                  false
% 6.94/1.49  --bmc1_k_induction                      false
% 6.94/1.49  --bmc1_non_equiv_states                 false
% 6.94/1.49  --bmc1_deadlock                         false
% 6.94/1.49  --bmc1_ucm                              false
% 6.94/1.49  --bmc1_add_unsat_core                   none
% 6.94/1.49  --bmc1_unsat_core_children              false
% 6.94/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.94/1.49  --bmc1_out_stat                         full
% 6.94/1.49  --bmc1_ground_init                      false
% 6.94/1.49  --bmc1_pre_inst_next_state              false
% 6.94/1.49  --bmc1_pre_inst_state                   false
% 6.94/1.49  --bmc1_pre_inst_reach_state             false
% 6.94/1.49  --bmc1_out_unsat_core                   false
% 6.94/1.49  --bmc1_aig_witness_out                  false
% 6.94/1.49  --bmc1_verbose                          false
% 6.94/1.49  --bmc1_dump_clauses_tptp                false
% 6.94/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.94/1.49  --bmc1_dump_file                        -
% 6.94/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.94/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.94/1.49  --bmc1_ucm_extend_mode                  1
% 6.94/1.49  --bmc1_ucm_init_mode                    2
% 6.94/1.49  --bmc1_ucm_cone_mode                    none
% 6.94/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.94/1.49  --bmc1_ucm_relax_model                  4
% 6.94/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.94/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.94/1.49  --bmc1_ucm_layered_model                none
% 6.94/1.49  --bmc1_ucm_max_lemma_size               10
% 6.94/1.49  
% 6.94/1.49  ------ AIG Options
% 6.94/1.49  
% 6.94/1.49  --aig_mode                              false
% 6.94/1.49  
% 6.94/1.49  ------ Instantiation Options
% 6.94/1.49  
% 6.94/1.49  --instantiation_flag                    true
% 6.94/1.49  --inst_sos_flag                         true
% 6.94/1.49  --inst_sos_phase                        true
% 6.94/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.94/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.94/1.49  --inst_lit_sel_side                     none
% 6.94/1.49  --inst_solver_per_active                1400
% 6.94/1.49  --inst_solver_calls_frac                1.
% 6.94/1.49  --inst_passive_queue_type               priority_queues
% 6.94/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.94/1.49  --inst_passive_queues_freq              [25;2]
% 6.94/1.49  --inst_dismatching                      true
% 6.94/1.49  --inst_eager_unprocessed_to_passive     true
% 6.94/1.49  --inst_prop_sim_given                   true
% 6.94/1.49  --inst_prop_sim_new                     false
% 6.94/1.49  --inst_subs_new                         false
% 6.94/1.49  --inst_eq_res_simp                      false
% 6.94/1.49  --inst_subs_given                       false
% 6.94/1.49  --inst_orphan_elimination               true
% 6.94/1.49  --inst_learning_loop_flag               true
% 6.94/1.49  --inst_learning_start                   3000
% 6.94/1.49  --inst_learning_factor                  2
% 6.94/1.49  --inst_start_prop_sim_after_learn       3
% 6.94/1.49  --inst_sel_renew                        solver
% 6.94/1.49  --inst_lit_activity_flag                true
% 6.94/1.49  --inst_restr_to_given                   false
% 6.94/1.49  --inst_activity_threshold               500
% 6.94/1.49  --inst_out_proof                        true
% 6.94/1.49  
% 6.94/1.49  ------ Resolution Options
% 6.94/1.49  
% 6.94/1.49  --resolution_flag                       false
% 6.94/1.49  --res_lit_sel                           adaptive
% 6.94/1.49  --res_lit_sel_side                      none
% 6.94/1.49  --res_ordering                          kbo
% 6.94/1.49  --res_to_prop_solver                    active
% 6.94/1.49  --res_prop_simpl_new                    false
% 6.94/1.49  --res_prop_simpl_given                  true
% 6.94/1.49  --res_passive_queue_type                priority_queues
% 6.94/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.94/1.49  --res_passive_queues_freq               [15;5]
% 6.94/1.49  --res_forward_subs                      full
% 6.94/1.49  --res_backward_subs                     full
% 6.94/1.49  --res_forward_subs_resolution           true
% 6.94/1.49  --res_backward_subs_resolution          true
% 6.94/1.49  --res_orphan_elimination                true
% 6.94/1.49  --res_time_limit                        2.
% 6.94/1.49  --res_out_proof                         true
% 6.94/1.49  
% 6.94/1.49  ------ Superposition Options
% 6.94/1.49  
% 6.94/1.49  --superposition_flag                    true
% 6.94/1.49  --sup_passive_queue_type                priority_queues
% 6.94/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.94/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.94/1.49  --demod_completeness_check              fast
% 6.94/1.49  --demod_use_ground                      true
% 6.94/1.49  --sup_to_prop_solver                    passive
% 6.94/1.49  --sup_prop_simpl_new                    true
% 6.94/1.49  --sup_prop_simpl_given                  true
% 6.94/1.49  --sup_fun_splitting                     true
% 6.94/1.49  --sup_smt_interval                      50000
% 6.94/1.49  
% 6.94/1.49  ------ Superposition Simplification Setup
% 6.94/1.49  
% 6.94/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.94/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.94/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.94/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.94/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.94/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.94/1.49  --sup_immed_triv                        [TrivRules]
% 6.94/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.94/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.94/1.49  --sup_immed_bw_main                     []
% 6.94/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.94/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.94/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.94/1.49  --sup_input_bw                          []
% 6.94/1.49  
% 6.94/1.49  ------ Combination Options
% 6.94/1.49  
% 6.94/1.49  --comb_res_mult                         3
% 6.94/1.49  --comb_sup_mult                         2
% 6.94/1.49  --comb_inst_mult                        10
% 6.94/1.49  
% 6.94/1.49  ------ Debug Options
% 6.94/1.49  
% 6.94/1.49  --dbg_backtrace                         false
% 6.94/1.49  --dbg_dump_prop_clauses                 false
% 6.94/1.49  --dbg_dump_prop_clauses_file            -
% 6.94/1.49  --dbg_out_stat                          false
% 6.94/1.49  
% 6.94/1.49  
% 6.94/1.49  
% 6.94/1.49  
% 6.94/1.49  ------ Proving...
% 6.94/1.49  
% 6.94/1.49  
% 6.94/1.49  % SZS status Theorem for theBenchmark.p
% 6.94/1.49  
% 6.94/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.94/1.49  
% 6.94/1.49  fof(f17,axiom,(
% 6.94/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f33,plain,(
% 6.94/1.49    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(ennf_transformation,[],[f17])).
% 6.94/1.49  
% 6.94/1.49  fof(f58,plain,(
% 6.94/1.49    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(nnf_transformation,[],[f33])).
% 6.94/1.49  
% 6.94/1.49  fof(f103,plain,(
% 6.94/1.49    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.94/1.49    inference(cnf_transformation,[],[f58])).
% 6.94/1.49  
% 6.94/1.49  fof(f2,axiom,(
% 6.94/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f22,plain,(
% 6.94/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.94/1.49    inference(ennf_transformation,[],[f2])).
% 6.94/1.49  
% 6.94/1.49  fof(f42,plain,(
% 6.94/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.94/1.49    inference(nnf_transformation,[],[f22])).
% 6.94/1.49  
% 6.94/1.49  fof(f43,plain,(
% 6.94/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.94/1.49    inference(rectify,[],[f42])).
% 6.94/1.49  
% 6.94/1.49  fof(f44,plain,(
% 6.94/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 6.94/1.49    introduced(choice_axiom,[])).
% 6.94/1.49  
% 6.94/1.49  fof(f45,plain,(
% 6.94/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.94/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 6.94/1.49  
% 6.94/1.49  fof(f69,plain,(
% 6.94/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f45])).
% 6.94/1.49  
% 6.94/1.49  fof(f6,axiom,(
% 6.94/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f21,plain,(
% 6.94/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.94/1.49    inference(rectify,[],[f6])).
% 6.94/1.49  
% 6.94/1.49  fof(f24,plain,(
% 6.94/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 6.94/1.49    inference(ennf_transformation,[],[f21])).
% 6.94/1.49  
% 6.94/1.49  fof(f52,plain,(
% 6.94/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 6.94/1.49    introduced(choice_axiom,[])).
% 6.94/1.49  
% 6.94/1.49  fof(f53,plain,(
% 6.94/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 6.94/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f52])).
% 6.94/1.49  
% 6.94/1.49  fof(f82,plain,(
% 6.94/1.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f53])).
% 6.94/1.49  
% 6.94/1.49  fof(f4,axiom,(
% 6.94/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f51,plain,(
% 6.94/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.94/1.49    inference(nnf_transformation,[],[f4])).
% 6.94/1.49  
% 6.94/1.49  fof(f78,plain,(
% 6.94/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f51])).
% 6.94/1.49  
% 6.94/1.49  fof(f70,plain,(
% 6.94/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f45])).
% 6.94/1.49  
% 6.94/1.49  fof(f19,conjecture,(
% 6.94/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f20,negated_conjecture,(
% 6.94/1.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 6.94/1.49    inference(negated_conjecture,[],[f19])).
% 6.94/1.49  
% 6.94/1.49  fof(f36,plain,(
% 6.94/1.49    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(ennf_transformation,[],[f20])).
% 6.94/1.49  
% 6.94/1.49  fof(f37,plain,(
% 6.94/1.49    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(flattening,[],[f36])).
% 6.94/1.49  
% 6.94/1.49  fof(f63,plain,(
% 6.94/1.49    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(nnf_transformation,[],[f37])).
% 6.94/1.49  
% 6.94/1.49  fof(f65,plain,(
% 6.94/1.49    ( ! [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k3_subset_1(X0,sK7) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,sK7)) & (~r2_hidden(X3,sK7) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(sK7,k1_zfmisc_1(X0)))) )),
% 6.94/1.49    introduced(choice_axiom,[])).
% 6.94/1.49  
% 6.94/1.49  fof(f64,plain,(
% 6.94/1.49    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k3_subset_1(sK5,X2) != sK6 & ! [X3] : (((r2_hidden(X3,sK6) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,sK6))) | ~m1_subset_1(X3,sK5)) & m1_subset_1(X2,k1_zfmisc_1(sK5))) & m1_subset_1(sK6,k1_zfmisc_1(sK5)))),
% 6.94/1.49    introduced(choice_axiom,[])).
% 6.94/1.49  
% 6.94/1.49  fof(f66,plain,(
% 6.94/1.49    (k3_subset_1(sK5,sK7) != sK6 & ! [X3] : (((r2_hidden(X3,sK6) | r2_hidden(X3,sK7)) & (~r2_hidden(X3,sK7) | ~r2_hidden(X3,sK6))) | ~m1_subset_1(X3,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(sK5))) & m1_subset_1(sK6,k1_zfmisc_1(sK5))),
% 6.94/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f63,f65,f64])).
% 6.94/1.49  
% 6.94/1.49  fof(f107,plain,(
% 6.94/1.49    m1_subset_1(sK6,k1_zfmisc_1(sK5))),
% 6.94/1.49    inference(cnf_transformation,[],[f66])).
% 6.94/1.49  
% 6.94/1.49  fof(f15,axiom,(
% 6.94/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f31,plain,(
% 6.94/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(ennf_transformation,[],[f15])).
% 6.94/1.49  
% 6.94/1.49  fof(f99,plain,(
% 6.94/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.94/1.49    inference(cnf_transformation,[],[f31])).
% 6.94/1.49  
% 6.94/1.49  fof(f71,plain,(
% 6.94/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f45])).
% 6.94/1.49  
% 6.94/1.49  fof(f13,axiom,(
% 6.94/1.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f29,plain,(
% 6.94/1.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 6.94/1.49    inference(ennf_transformation,[],[f13])).
% 6.94/1.49  
% 6.94/1.49  fof(f56,plain,(
% 6.94/1.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 6.94/1.49    inference(nnf_transformation,[],[f29])).
% 6.94/1.49  
% 6.94/1.49  fof(f95,plain,(
% 6.94/1.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f56])).
% 6.94/1.49  
% 6.94/1.49  fof(f1,axiom,(
% 6.94/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f38,plain,(
% 6.94/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 6.94/1.49    inference(nnf_transformation,[],[f1])).
% 6.94/1.49  
% 6.94/1.49  fof(f39,plain,(
% 6.94/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.94/1.49    inference(rectify,[],[f38])).
% 6.94/1.49  
% 6.94/1.49  fof(f40,plain,(
% 6.94/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 6.94/1.49    introduced(choice_axiom,[])).
% 6.94/1.49  
% 6.94/1.49  fof(f41,plain,(
% 6.94/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.94/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 6.94/1.49  
% 6.94/1.49  fof(f67,plain,(
% 6.94/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f41])).
% 6.94/1.49  
% 6.94/1.49  fof(f110,plain,(
% 6.94/1.49    ( ! [X3] : (r2_hidden(X3,sK6) | r2_hidden(X3,sK7) | ~m1_subset_1(X3,sK5)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f66])).
% 6.94/1.49  
% 6.94/1.49  fof(f83,plain,(
% 6.94/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f53])).
% 6.94/1.49  
% 6.94/1.49  fof(f79,plain,(
% 6.94/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 6.94/1.49    inference(cnf_transformation,[],[f51])).
% 6.94/1.49  
% 6.94/1.49  fof(f81,plain,(
% 6.94/1.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f53])).
% 6.94/1.49  
% 6.94/1.49  fof(f109,plain,(
% 6.94/1.49    ( ! [X3] : (~r2_hidden(X3,sK7) | ~r2_hidden(X3,sK6) | ~m1_subset_1(X3,sK5)) )),
% 6.94/1.49    inference(cnf_transformation,[],[f66])).
% 6.94/1.49  
% 6.94/1.49  fof(f14,axiom,(
% 6.94/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f30,plain,(
% 6.94/1.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(ennf_transformation,[],[f14])).
% 6.94/1.49  
% 6.94/1.49  fof(f98,plain,(
% 6.94/1.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.94/1.49    inference(cnf_transformation,[],[f30])).
% 6.94/1.49  
% 6.94/1.49  fof(f16,axiom,(
% 6.94/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f32,plain,(
% 6.94/1.49    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(ennf_transformation,[],[f16])).
% 6.94/1.49  
% 6.94/1.49  fof(f57,plain,(
% 6.94/1.49    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(nnf_transformation,[],[f32])).
% 6.94/1.49  
% 6.94/1.49  fof(f100,plain,(
% 6.94/1.49    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.94/1.49    inference(cnf_transformation,[],[f57])).
% 6.94/1.49  
% 6.94/1.49  fof(f18,axiom,(
% 6.94/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 6.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.94/1.49  
% 6.94/1.49  fof(f34,plain,(
% 6.94/1.49    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(ennf_transformation,[],[f18])).
% 6.94/1.49  
% 6.94/1.49  fof(f35,plain,(
% 6.94/1.49    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(flattening,[],[f34])).
% 6.94/1.49  
% 6.94/1.49  fof(f59,plain,(
% 6.94/1.49    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(nnf_transformation,[],[f35])).
% 6.94/1.49  
% 6.94/1.49  fof(f60,plain,(
% 6.94/1.49    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(flattening,[],[f59])).
% 6.94/1.49  
% 6.94/1.49  fof(f61,plain,(
% 6.94/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1)) & (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1)) & m1_subset_1(sK4(X0,X1,X2),X0)))),
% 6.94/1.49    introduced(choice_axiom,[])).
% 6.94/1.49  
% 6.94/1.49  fof(f62,plain,(
% 6.94/1.49    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1)) & (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1)) & m1_subset_1(sK4(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.94/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).
% 6.94/1.49  
% 6.94/1.49  fof(f106,plain,(
% 6.94/1.49    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.94/1.49    inference(cnf_transformation,[],[f62])).
% 6.94/1.49  
% 6.94/1.49  fof(f105,plain,(
% 6.94/1.49    ( ! [X2,X0,X1] : (X1 = X2 | r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.94/1.49    inference(cnf_transformation,[],[f62])).
% 6.94/1.49  
% 6.94/1.49  fof(f104,plain,(
% 6.94/1.49    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK4(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.94/1.49    inference(cnf_transformation,[],[f62])).
% 6.94/1.49  
% 6.94/1.49  fof(f111,plain,(
% 6.94/1.49    k3_subset_1(sK5,sK7) != sK6),
% 6.94/1.49    inference(cnf_transformation,[],[f66])).
% 6.94/1.49  
% 6.94/1.49  fof(f108,plain,(
% 6.94/1.49    m1_subset_1(sK7,k1_zfmisc_1(sK5))),
% 6.94/1.49    inference(cnf_transformation,[],[f66])).
% 6.94/1.49  
% 6.94/1.49  cnf(c_35,plain,
% 6.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.94/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.94/1.49      | r1_xboole_0(X0,k3_subset_1(X1,X2))
% 6.94/1.49      | ~ r1_tarski(X0,X2) ),
% 6.94/1.49      inference(cnf_transformation,[],[f103]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_4575,plain,
% 6.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
% 6.94/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
% 6.94/1.49      | r1_xboole_0(X0,k3_subset_1(sK5,sK7))
% 6.94/1.49      | ~ r1_tarski(X0,sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_35]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_19697,plain,
% 6.94/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
% 6.94/1.49      | r1_xboole_0(sK7,k3_subset_1(sK5,sK7))
% 6.94/1.49      | ~ r1_tarski(sK7,sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_4575]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_4,plain,
% 6.94/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 6.94/1.49      inference(cnf_transformation,[],[f69]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_4153,plain,
% 6.94/1.49      ( ~ r1_tarski(sK6,X0) | r2_hidden(X1,X0) | ~ r2_hidden(X1,sK6) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_6696,plain,
% 6.94/1.49      ( ~ r1_tarski(sK6,X0)
% 6.94/1.49      | r2_hidden(sK3(X1,sK7),X0)
% 6.94/1.49      | ~ r2_hidden(sK3(X1,sK7),sK6) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_4153]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_14056,plain,
% 6.94/1.49      ( ~ r1_tarski(sK6,X0)
% 6.94/1.49      | r2_hidden(sK3(sK6,sK7),X0)
% 6.94/1.49      | ~ r2_hidden(sK3(sK6,sK7),sK6) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_6696]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_14058,plain,
% 6.94/1.49      ( r1_tarski(sK6,X0) != iProver_top
% 6.94/1.49      | r2_hidden(sK3(sK6,sK7),X0) = iProver_top
% 6.94/1.49      | r2_hidden(sK3(sK6,sK7),sK6) != iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_14056]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_14060,plain,
% 6.94/1.49      ( r1_tarski(sK6,sK5) != iProver_top
% 6.94/1.49      | r2_hidden(sK3(sK6,sK7),sK6) != iProver_top
% 6.94/1.49      | r2_hidden(sK3(sK6,sK7),sK5) = iProver_top ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_14058]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_6690,plain,
% 6.94/1.49      ( ~ r1_tarski(sK6,X0)
% 6.94/1.49      | r2_hidden(sK4(X1,k3_subset_1(sK5,sK7),sK6),X0)
% 6.94/1.49      | ~ r2_hidden(sK4(X1,k3_subset_1(sK5,sK7),sK6),sK6) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_4153]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_13907,plain,
% 6.94/1.49      ( ~ r1_tarski(sK6,k3_subset_1(sK5,sK7))
% 6.94/1.49      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7))
% 6.94/1.49      | ~ r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_6690]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_13908,plain,
% 6.94/1.49      ( r1_tarski(sK6,k3_subset_1(sK5,sK7)) != iProver_top
% 6.94/1.49      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) = iProver_top
% 6.94/1.49      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6) != iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_13907]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_13910,plain,
% 6.94/1.49      ( r1_tarski(sK6,k3_subset_1(sK5,sK7)) != iProver_top
% 6.94/1.49      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) = iProver_top
% 6.94/1.49      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK6) != iProver_top ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_13908]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_15,plain,
% 6.94/1.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1) ),
% 6.94/1.49      inference(cnf_transformation,[],[f82]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_6207,plain,
% 6.94/1.49      ( r1_xboole_0(X0,sK7) | r2_hidden(sK3(X0,sK7),sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_11653,plain,
% 6.94/1.49      ( r1_xboole_0(sK6,sK7) | r2_hidden(sK3(sK6,sK7),sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_6207]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_11655,plain,
% 6.94/1.49      ( r1_xboole_0(sK6,sK7) = iProver_top
% 6.94/1.49      | r2_hidden(sK3(sK6,sK7),sK7) = iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_11653]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_12,plain,
% 6.94/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 6.94/1.49      inference(cnf_transformation,[],[f78]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_10618,plain,
% 6.94/1.49      ( ~ r1_xboole_0(sK7,k3_subset_1(sK5,sK7))
% 6.94/1.49      | k3_xboole_0(sK7,k3_subset_1(sK5,sK7)) = k1_xboole_0 ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_3,plain,
% 6.94/1.49      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 6.94/1.49      inference(cnf_transformation,[],[f70]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_1770,plain,
% 6.94/1.49      ( r1_tarski(X0,X1) = iProver_top
% 6.94/1.49      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_44,negated_conjecture,
% 6.94/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
% 6.94/1.49      inference(cnf_transformation,[],[f107]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_1733,plain,
% 6.94/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_32,plain,
% 6.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.94/1.49      | ~ r2_hidden(X2,X0)
% 6.94/1.49      | r2_hidden(X2,X1) ),
% 6.94/1.49      inference(cnf_transformation,[],[f99]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_1744,plain,
% 6.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.94/1.49      | r2_hidden(X2,X0) != iProver_top
% 6.94/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_5573,plain,
% 6.94/1.49      ( r2_hidden(X0,sK6) != iProver_top
% 6.94/1.49      | r2_hidden(X0,sK5) = iProver_top ),
% 6.94/1.49      inference(superposition,[status(thm)],[c_1733,c_1744]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_5751,plain,
% 6.94/1.49      ( r1_tarski(sK6,X0) = iProver_top
% 6.94/1.49      | r2_hidden(sK1(sK6,X0),sK5) = iProver_top ),
% 6.94/1.49      inference(superposition,[status(thm)],[c_1770,c_5573]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_2,plain,
% 6.94/1.49      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 6.94/1.49      inference(cnf_transformation,[],[f71]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_1771,plain,
% 6.94/1.49      ( r1_tarski(X0,X1) = iProver_top
% 6.94/1.49      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_10542,plain,
% 6.94/1.49      ( r1_tarski(sK6,sK5) = iProver_top ),
% 6.94/1.49      inference(superposition,[status(thm)],[c_5751,c_1771]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_29,plain,
% 6.94/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 6.94/1.49      inference(cnf_transformation,[],[f95]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_1,plain,
% 6.94/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 6.94/1.49      inference(cnf_transformation,[],[f67]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_248,plain,
% 6.94/1.49      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 6.94/1.49      inference(global_propositional_subsumption,
% 6.94/1.49                [status(thm)],
% 6.94/1.49                [c_29,c_1]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_249,plain,
% 6.94/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 6.94/1.49      inference(renaming,[status(thm)],[c_248]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_2024,plain,
% 6.94/1.49      ( m1_subset_1(sK3(X0,sK7),sK5) | ~ r2_hidden(sK3(X0,sK7),sK5) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_249]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_7268,plain,
% 6.94/1.49      ( m1_subset_1(sK3(sK6,sK7),sK5) | ~ r2_hidden(sK3(sK6,sK7),sK5) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_2024]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_7269,plain,
% 6.94/1.49      ( m1_subset_1(sK3(sK6,sK7),sK5) = iProver_top
% 6.94/1.49      | r2_hidden(sK3(sK6,sK7),sK5) != iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_7268]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_41,negated_conjecture,
% 6.94/1.49      ( ~ m1_subset_1(X0,sK5) | r2_hidden(X0,sK6) | r2_hidden(X0,sK7) ),
% 6.94/1.49      inference(cnf_transformation,[],[f110]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_6441,plain,
% 6.94/1.49      ( ~ m1_subset_1(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK5)
% 6.94/1.49      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK6)
% 6.94/1.49      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_41]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_6442,plain,
% 6.94/1.49      ( m1_subset_1(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK5) != iProver_top
% 6.94/1.49      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK6) = iProver_top
% 6.94/1.49      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK7) = iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_6441]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_14,plain,
% 6.94/1.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 6.94/1.49      inference(cnf_transformation,[],[f83]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_3474,plain,
% 6.94/1.49      ( ~ r1_xboole_0(X0,k3_subset_1(sK5,sK7))
% 6.94/1.49      | ~ r2_hidden(sK4(X1,k3_subset_1(sK5,sK7),sK6),X0)
% 6.94/1.49      | ~ r2_hidden(sK4(X1,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_5716,plain,
% 6.94/1.49      ( ~ r1_xboole_0(sK7,k3_subset_1(sK5,sK7))
% 6.94/1.49      | ~ r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7))
% 6.94/1.49      | ~ r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_3474]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_5719,plain,
% 6.94/1.49      ( r1_xboole_0(sK7,k3_subset_1(sK5,sK7)) != iProver_top
% 6.94/1.49      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) != iProver_top
% 6.94/1.49      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK7) != iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_5716]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_5721,plain,
% 6.94/1.49      ( r1_xboole_0(sK7,k3_subset_1(sK5,sK7)) != iProver_top
% 6.94/1.49      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) != iProver_top
% 6.94/1.49      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK7) != iProver_top ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_5719]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_11,plain,
% 6.94/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 6.94/1.49      inference(cnf_transformation,[],[f79]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_3114,plain,
% 6.94/1.49      ( r1_xboole_0(sK7,X0) | k3_xboole_0(sK7,X0) != k1_xboole_0 ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_5715,plain,
% 6.94/1.49      ( r1_xboole_0(sK7,k3_subset_1(sK5,sK7))
% 6.94/1.49      | k3_xboole_0(sK7,k3_subset_1(sK5,sK7)) != k1_xboole_0 ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_3114]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_5717,plain,
% 6.94/1.49      ( k3_xboole_0(sK7,k3_subset_1(sK5,sK7)) != k1_xboole_0
% 6.94/1.49      | r1_xboole_0(sK7,k3_subset_1(sK5,sK7)) = iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_5715]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_16,plain,
% 6.94/1.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0) ),
% 6.94/1.49      inference(cnf_transformation,[],[f81]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_2716,plain,
% 6.94/1.49      ( r1_xboole_0(sK6,X0) | r2_hidden(sK3(sK6,X0),sK6) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_5620,plain,
% 6.94/1.49      ( r1_xboole_0(sK6,sK7) | r2_hidden(sK3(sK6,sK7),sK6) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_2716]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_5621,plain,
% 6.94/1.49      ( r1_xboole_0(sK6,sK7) = iProver_top
% 6.94/1.49      | r2_hidden(sK3(sK6,sK7),sK6) = iProver_top ),
% 6.94/1.49      inference(predicate_to_equality,[status(thm)],[c_5620]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_2918,plain,
% 6.94/1.49      ( r1_tarski(X0,sK7) | r2_hidden(sK1(X0,sK7),X0) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_4171,plain,
% 6.94/1.49      ( r1_tarski(sK7,sK7) | r2_hidden(sK1(sK7,sK7),sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_2918]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_2917,plain,
% 6.94/1.49      ( r1_tarski(X0,sK7) | ~ r2_hidden(sK1(X0,sK7),sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_4172,plain,
% 6.94/1.49      ( r1_tarski(sK7,sK7) | ~ r2_hidden(sK1(sK7,sK7),sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_2917]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_42,negated_conjecture,
% 6.94/1.49      ( ~ m1_subset_1(X0,sK5)
% 6.94/1.49      | ~ r2_hidden(X0,sK6)
% 6.94/1.49      | ~ r2_hidden(X0,sK7) ),
% 6.94/1.49      inference(cnf_transformation,[],[f109]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_2006,plain,
% 6.94/1.49      ( ~ m1_subset_1(sK3(sK6,X0),sK5)
% 6.94/1.49      | ~ r2_hidden(sK3(sK6,X0),sK6)
% 6.94/1.49      | ~ r2_hidden(sK3(sK6,X0),sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_42]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_3682,plain,
% 6.94/1.49      ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
% 6.94/1.49      | ~ r2_hidden(sK3(sK6,sK7),sK6)
% 6.94/1.49      | ~ r2_hidden(sK3(sK6,sK7),sK7) ),
% 6.94/1.49      inference(instantiation,[status(thm)],[c_2006]) ).
% 6.94/1.49  
% 6.94/1.49  cnf(c_3685,plain,
% 6.94/1.49      ( m1_subset_1(sK3(sK6,sK7),sK5) != iProver_top
% 6.94/1.49      | r2_hidden(sK3(sK6,sK7),sK6) != iProver_top
% 6.94/1.49      | r2_hidden(sK3(sK6,sK7),sK7) != iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_3682]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_31,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.94/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 6.94/1.50      inference(cnf_transformation,[],[f98]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_2410,plain,
% 6.94/1.50      ( m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(sK5))
% 6.94/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
% 6.94/1.50      inference(instantiation,[status(thm)],[c_31]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_2411,plain,
% 6.94/1.50      ( m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(sK5)) = iProver_top
% 6.94/1.50      | m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_2410]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_34,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.94/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.94/1.50      | ~ r1_xboole_0(X0,X2)
% 6.94/1.50      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 6.94/1.50      inference(cnf_transformation,[],[f100]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_2388,plain,
% 6.94/1.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
% 6.94/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
% 6.94/1.50      | ~ r1_xboole_0(sK6,sK7)
% 6.94/1.50      | r1_tarski(sK6,k3_subset_1(sK5,sK7)) ),
% 6.94/1.50      inference(instantiation,[status(thm)],[c_34]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_2389,plain,
% 6.94/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
% 6.94/1.50      | m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top
% 6.94/1.50      | r1_xboole_0(sK6,sK7) != iProver_top
% 6.94/1.50      | r1_tarski(sK6,k3_subset_1(sK5,sK7)) = iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_2388]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_37,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.94/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.94/1.50      | ~ r2_hidden(sK4(X1,X0,X2),X2)
% 6.94/1.50      | ~ r2_hidden(sK4(X1,X0,X2),X0)
% 6.94/1.50      | X0 = X2 ),
% 6.94/1.50      inference(cnf_transformation,[],[f106]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1820,plain,
% 6.94/1.50      ( ~ m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0))
% 6.94/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 6.94/1.50      | ~ r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7))
% 6.94/1.50      | ~ r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6)
% 6.94/1.50      | k3_subset_1(sK5,sK7) = sK6 ),
% 6.94/1.50      inference(instantiation,[status(thm)],[c_37]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1831,plain,
% 6.94/1.50      ( k3_subset_1(sK5,sK7) = sK6
% 6.94/1.50      | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0)) != iProver_top
% 6.94/1.50      | m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
% 6.94/1.50      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) != iProver_top
% 6.94/1.50      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6) != iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_1820]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1833,plain,
% 6.94/1.50      ( k3_subset_1(sK5,sK7) = sK6
% 6.94/1.50      | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(sK5)) != iProver_top
% 6.94/1.50      | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
% 6.94/1.50      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) != iProver_top
% 6.94/1.50      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK6) != iProver_top ),
% 6.94/1.50      inference(instantiation,[status(thm)],[c_1831]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_38,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.94/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.94/1.50      | r2_hidden(sK4(X1,X0,X2),X2)
% 6.94/1.50      | r2_hidden(sK4(X1,X0,X2),X0)
% 6.94/1.50      | X0 = X2 ),
% 6.94/1.50      inference(cnf_transformation,[],[f105]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1821,plain,
% 6.94/1.50      ( ~ m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0))
% 6.94/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 6.94/1.50      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7))
% 6.94/1.50      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6)
% 6.94/1.50      | k3_subset_1(sK5,sK7) = sK6 ),
% 6.94/1.50      inference(instantiation,[status(thm)],[c_38]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1827,plain,
% 6.94/1.50      ( k3_subset_1(sK5,sK7) = sK6
% 6.94/1.50      | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0)) != iProver_top
% 6.94/1.50      | m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
% 6.94/1.50      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) = iProver_top
% 6.94/1.50      | r2_hidden(sK4(X0,k3_subset_1(sK5,sK7),sK6),sK6) = iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_1821]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1829,plain,
% 6.94/1.50      ( k3_subset_1(sK5,sK7) = sK6
% 6.94/1.50      | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(sK5)) != iProver_top
% 6.94/1.50      | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
% 6.94/1.50      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),k3_subset_1(sK5,sK7)) = iProver_top
% 6.94/1.50      | r2_hidden(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK6) = iProver_top ),
% 6.94/1.50      inference(instantiation,[status(thm)],[c_1827]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_39,plain,
% 6.94/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.94/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.94/1.50      | m1_subset_1(sK4(X1,X0,X2),X1)
% 6.94/1.50      | X0 = X2 ),
% 6.94/1.50      inference(cnf_transformation,[],[f104]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1822,plain,
% 6.94/1.50      ( m1_subset_1(sK4(X0,k3_subset_1(sK5,sK7),sK6),X0)
% 6.94/1.50      | ~ m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0))
% 6.94/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 6.94/1.50      | k3_subset_1(sK5,sK7) = sK6 ),
% 6.94/1.50      inference(instantiation,[status(thm)],[c_39]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1823,plain,
% 6.94/1.50      ( k3_subset_1(sK5,sK7) = sK6
% 6.94/1.50      | m1_subset_1(sK4(X0,k3_subset_1(sK5,sK7),sK6),X0) = iProver_top
% 6.94/1.50      | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(X0)) != iProver_top
% 6.94/1.50      | m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_1822]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_1825,plain,
% 6.94/1.50      ( k3_subset_1(sK5,sK7) = sK6
% 6.94/1.50      | m1_subset_1(sK4(sK5,k3_subset_1(sK5,sK7),sK6),sK5) = iProver_top
% 6.94/1.50      | m1_subset_1(k3_subset_1(sK5,sK7),k1_zfmisc_1(sK5)) != iProver_top
% 6.94/1.50      | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top ),
% 6.94/1.50      inference(instantiation,[status(thm)],[c_1823]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_40,negated_conjecture,
% 6.94/1.50      ( k3_subset_1(sK5,sK7) != sK6 ),
% 6.94/1.50      inference(cnf_transformation,[],[f111]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_43,negated_conjecture,
% 6.94/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
% 6.94/1.50      inference(cnf_transformation,[],[f108]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_46,plain,
% 6.94/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) = iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(c_45,plain,
% 6.94/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
% 6.94/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 6.94/1.50  
% 6.94/1.50  cnf(contradiction,plain,
% 6.94/1.50      ( $false ),
% 6.94/1.50      inference(minisat,
% 6.94/1.50                [status(thm)],
% 6.94/1.50                [c_19697,c_14060,c_13910,c_11655,c_10618,c_10542,c_7269,
% 6.94/1.50                 c_6442,c_5721,c_5717,c_5621,c_4171,c_4172,c_3685,c_2411,
% 6.94/1.50                 c_2389,c_1833,c_1829,c_1825,c_40,c_46,c_43,c_45]) ).
% 6.94/1.50  
% 6.94/1.50  
% 6.94/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.94/1.50  
% 6.94/1.50  ------                               Statistics
% 6.94/1.50  
% 6.94/1.50  ------ General
% 6.94/1.50  
% 6.94/1.50  abstr_ref_over_cycles:                  0
% 6.94/1.50  abstr_ref_under_cycles:                 0
% 6.94/1.50  gc_basic_clause_elim:                   0
% 6.94/1.50  forced_gc_time:                         0
% 6.94/1.50  parsing_time:                           0.016
% 6.94/1.50  unif_index_cands_time:                  0.
% 6.94/1.50  unif_index_add_time:                    0.
% 6.94/1.50  orderings_time:                         0.
% 6.94/1.50  out_proof_time:                         0.023
% 6.94/1.50  total_time:                             0.586
% 6.94/1.50  num_of_symbols:                         50
% 6.94/1.50  num_of_terms:                           19583
% 6.94/1.50  
% 6.94/1.50  ------ Preprocessing
% 6.94/1.50  
% 6.94/1.50  num_of_splits:                          0
% 6.94/1.50  num_of_split_atoms:                     0
% 6.94/1.50  num_of_reused_defs:                     0
% 6.94/1.50  num_eq_ax_congr_red:                    54
% 6.94/1.50  num_of_sem_filtered_clauses:            1
% 6.94/1.50  num_of_subtypes:                        0
% 6.94/1.50  monotx_restored_types:                  0
% 6.94/1.50  sat_num_of_epr_types:                   0
% 6.94/1.50  sat_num_of_non_cyclic_types:            0
% 6.94/1.50  sat_guarded_non_collapsed_types:        0
% 6.94/1.50  num_pure_diseq_elim:                    0
% 6.94/1.50  simp_replaced_by:                       0
% 6.94/1.50  res_preprocessed:                       195
% 6.94/1.50  prep_upred:                             0
% 6.94/1.50  prep_unflattend:                        0
% 6.94/1.50  smt_new_axioms:                         0
% 6.94/1.50  pred_elim_cands:                        5
% 6.94/1.50  pred_elim:                              0
% 6.94/1.50  pred_elim_cl:                           0
% 6.94/1.50  pred_elim_cycles:                       2
% 6.94/1.50  merged_defs:                            8
% 6.94/1.50  merged_defs_ncl:                        0
% 6.94/1.50  bin_hyper_res:                          8
% 6.94/1.50  prep_cycles:                            4
% 6.94/1.50  pred_elim_time:                         0.001
% 6.94/1.50  splitting_time:                         0.
% 6.94/1.50  sem_filter_time:                        0.
% 6.94/1.50  monotx_time:                            0.001
% 6.94/1.50  subtype_inf_time:                       0.
% 6.94/1.50  
% 6.94/1.50  ------ Problem properties
% 6.94/1.50  
% 6.94/1.50  clauses:                                44
% 6.94/1.50  conjectures:                            5
% 6.94/1.50  epr:                                    13
% 6.94/1.50  horn:                                   34
% 6.94/1.50  ground:                                 3
% 6.94/1.50  unary:                                  6
% 6.94/1.50  binary:                                 16
% 6.94/1.50  lits:                                   114
% 6.94/1.50  lits_eq:                                12
% 6.94/1.50  fd_pure:                                0
% 6.94/1.50  fd_pseudo:                              0
% 6.94/1.50  fd_cond:                                0
% 6.94/1.50  fd_pseudo_cond:                         7
% 6.94/1.50  ac_symbols:                             0
% 6.94/1.50  
% 6.94/1.50  ------ Propositional Solver
% 6.94/1.50  
% 6.94/1.50  prop_solver_calls:                      30
% 6.94/1.50  prop_fast_solver_calls:                 1608
% 6.94/1.50  smt_solver_calls:                       0
% 6.94/1.50  smt_fast_solver_calls:                  0
% 6.94/1.50  prop_num_of_clauses:                    10612
% 6.94/1.50  prop_preprocess_simplified:             25303
% 6.94/1.50  prop_fo_subsumed:                       57
% 6.94/1.50  prop_solver_time:                       0.
% 6.94/1.50  smt_solver_time:                        0.
% 6.94/1.50  smt_fast_solver_time:                   0.
% 6.94/1.50  prop_fast_solver_time:                  0.
% 6.94/1.50  prop_unsat_core_time:                   0.001
% 6.94/1.50  
% 6.94/1.50  ------ QBF
% 6.94/1.50  
% 6.94/1.50  qbf_q_res:                              0
% 6.94/1.50  qbf_num_tautologies:                    0
% 6.94/1.50  qbf_prep_cycles:                        0
% 6.94/1.50  
% 6.94/1.50  ------ BMC1
% 6.94/1.50  
% 6.94/1.50  bmc1_current_bound:                     -1
% 6.94/1.50  bmc1_last_solved_bound:                 -1
% 6.94/1.50  bmc1_unsat_core_size:                   -1
% 6.94/1.50  bmc1_unsat_core_parents_size:           -1
% 6.94/1.50  bmc1_merge_next_fun:                    0
% 6.94/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.94/1.50  
% 6.94/1.50  ------ Instantiation
% 6.94/1.50  
% 6.94/1.50  inst_num_of_clauses:                    2438
% 6.94/1.50  inst_num_in_passive:                    377
% 6.94/1.50  inst_num_in_active:                     842
% 6.94/1.50  inst_num_in_unprocessed:                1221
% 6.94/1.50  inst_num_of_loops:                      1057
% 6.94/1.50  inst_num_of_learning_restarts:          0
% 6.94/1.50  inst_num_moves_active_passive:          214
% 6.94/1.50  inst_lit_activity:                      0
% 6.94/1.50  inst_lit_activity_moves:                0
% 6.94/1.50  inst_num_tautologies:                   0
% 6.94/1.50  inst_num_prop_implied:                  0
% 6.94/1.50  inst_num_existing_simplified:           0
% 6.94/1.50  inst_num_eq_res_simplified:             0
% 6.94/1.50  inst_num_child_elim:                    0
% 6.94/1.50  inst_num_of_dismatching_blockings:      1735
% 6.94/1.50  inst_num_of_non_proper_insts:           2581
% 6.94/1.50  inst_num_of_duplicates:                 0
% 6.94/1.50  inst_inst_num_from_inst_to_res:         0
% 6.94/1.50  inst_dismatching_checking_time:         0.
% 6.94/1.50  
% 6.94/1.50  ------ Resolution
% 6.94/1.50  
% 6.94/1.50  res_num_of_clauses:                     0
% 6.94/1.50  res_num_in_passive:                     0
% 6.94/1.50  res_num_in_active:                      0
% 6.94/1.50  res_num_of_loops:                       199
% 6.94/1.50  res_forward_subset_subsumed:            42
% 6.94/1.50  res_backward_subset_subsumed:           4
% 6.94/1.50  res_forward_subsumed:                   0
% 6.94/1.50  res_backward_subsumed:                  0
% 6.94/1.50  res_forward_subsumption_resolution:     0
% 6.94/1.50  res_backward_subsumption_resolution:    0
% 6.94/1.50  res_clause_to_clause_subsumption:       3099
% 6.94/1.50  res_orphan_elimination:                 0
% 6.94/1.50  res_tautology_del:                      472
% 6.94/1.50  res_num_eq_res_simplified:              0
% 6.94/1.50  res_num_sel_changes:                    0
% 6.94/1.50  res_moves_from_active_to_pass:          0
% 6.94/1.50  
% 6.94/1.50  ------ Superposition
% 6.94/1.50  
% 6.94/1.50  sup_time_total:                         0.
% 6.94/1.50  sup_time_generating:                    0.
% 6.94/1.50  sup_time_sim_full:                      0.
% 6.94/1.50  sup_time_sim_immed:                     0.
% 6.94/1.50  
% 6.94/1.50  sup_num_of_clauses:                     786
% 6.94/1.50  sup_num_in_active:                      184
% 6.94/1.50  sup_num_in_passive:                     602
% 6.94/1.50  sup_num_of_loops:                       210
% 6.94/1.50  sup_fw_superposition:                   190
% 6.94/1.50  sup_bw_superposition:                   829
% 6.94/1.50  sup_immediate_simplified:               146
% 6.94/1.50  sup_given_eliminated:                   0
% 6.94/1.50  comparisons_done:                       0
% 6.94/1.50  comparisons_avoided:                    1
% 6.94/1.50  
% 6.94/1.50  ------ Simplifications
% 6.94/1.50  
% 6.94/1.50  
% 6.94/1.50  sim_fw_subset_subsumed:                 85
% 6.94/1.50  sim_bw_subset_subsumed:                 14
% 6.94/1.50  sim_fw_subsumed:                        56
% 6.94/1.50  sim_bw_subsumed:                        23
% 6.94/1.50  sim_fw_subsumption_res:                 0
% 6.94/1.50  sim_bw_subsumption_res:                 0
% 6.94/1.50  sim_tautology_del:                      57
% 6.94/1.50  sim_eq_tautology_del:                   4
% 6.94/1.50  sim_eq_res_simp:                        14
% 6.94/1.50  sim_fw_demodulated:                     0
% 6.94/1.50  sim_bw_demodulated:                     0
% 6.94/1.50  sim_light_normalised:                   0
% 6.94/1.50  sim_joinable_taut:                      0
% 6.94/1.50  sim_joinable_simp:                      0
% 6.94/1.50  sim_ac_normalised:                      0
% 6.94/1.50  sim_smt_subsumption:                    0
% 6.94/1.50  
%------------------------------------------------------------------------------
