%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:05 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 456 expanded)
%              Number of clauses        :   99 ( 158 expanded)
%              Number of leaves         :   28 (  96 expanded)
%              Depth                    :   23
%              Number of atoms          :  593 (1630 expanded)
%              Number of equality atoms :  227 ( 506 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
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

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f51])).

fof(f53,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK5) != sK6
        | ~ r1_tarski(k3_subset_1(sK5,sK6),sK6) )
      & ( k2_subset_1(sK5) = sK6
        | r1_tarski(k3_subset_1(sK5,sK6),sK6) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( k2_subset_1(sK5) != sK6
      | ~ r1_tarski(k3_subset_1(sK5,sK6),sK6) )
    & ( k2_subset_1(sK5) = sK6
      | r1_tarski(k3_subset_1(sK5,sK6),sK6) )
    & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f52,f53])).

fof(f92,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f113,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f87,f74])).

fof(f93,plain,
    ( k2_subset_1(sK5) = sK6
    | r1_tarski(k3_subset_1(sK5,sK6),sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f95,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f90,f85])).

fof(f105,plain,
    ( k3_subset_1(sK5,k1_xboole_0) = sK6
    | r1_tarski(k3_subset_1(sK5,sK6),sK6) ),
    inference(definition_unfolding,[],[f93,f95])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f102,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f86,f95])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f66,f74])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f100])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f71,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f101])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(nnf_transformation,[],[f22])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,
    ( k2_subset_1(sK5) != sK6
    | ~ r1_tarski(k3_subset_1(sK5,sK6),sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,
    ( k3_subset_1(sK5,k1_xboole_0) != sK6
    | ~ r1_tarski(k3_subset_1(sK5,sK6),sK6) ),
    inference(definition_unfolding,[],[f94,f95])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f112,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f78])).

cnf(c_1634,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2806,plain,
    ( X0 != X1
    | k3_subset_1(sK5,sK6) != X1
    | k3_subset_1(sK5,sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_4803,plain,
    ( X0 != k3_subset_1(X1,X2)
    | k3_subset_1(sK5,sK6) = X0
    | k3_subset_1(sK5,sK6) != k3_subset_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2806])).

cnf(c_10833,plain,
    ( k3_subset_1(sK5,sK6) != k3_subset_1(X0,X1)
    | k3_subset_1(sK5,sK6) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k3_subset_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_4803])).

cnf(c_10834,plain,
    ( k3_subset_1(sK5,sK6) != k3_subset_1(sK6,sK6)
    | k3_subset_1(sK5,sK6) = k5_xboole_0(sK6,k3_xboole_0(sK6,sK6))
    | k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)) != k3_subset_1(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_10833])).

cnf(c_18,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r2_hidden(sK3(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2274,plain,
    ( X0 = X1
    | r2_hidden(sK3(X1,X0),X0) = iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_505,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK5) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_506,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(sK5))
    | v1_xboole_0(k1_zfmisc_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_31,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_512,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(sK5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_506,c_31])).

cnf(c_2265,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2269,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3686,plain,
    ( r1_tarski(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_2269])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2273,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4307,plain,
    ( k3_xboole_0(sK6,sK5) = sK6 ),
    inference(superposition,[status(thm)],[c_3686,c_2273])).

cnf(c_4777,plain,
    ( k3_xboole_0(sK5,sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_0,c_4307])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_545,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_36])).

cnf(c_546,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = k3_subset_1(X0,sK6)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_2522,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK6)) = k3_subset_1(sK5,sK6) ),
    inference(equality_resolution,[status(thm)],[c_546])).

cnf(c_4923,plain,
    ( k3_subset_1(sK5,sK6) = k5_xboole_0(sK5,sK6) ),
    inference(demodulation,[status(thm)],[c_4777,c_2522])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK5,sK6),sK6)
    | k3_subset_1(sK5,k1_xboole_0) = sK6 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2267,plain,
    ( k3_subset_1(sK5,k1_xboole_0) = sK6
    | r1_tarski(k3_subset_1(sK5,sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_29,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2307,plain,
    ( sK6 = sK5
    | r1_tarski(k3_subset_1(sK5,sK6),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2267,c_29])).

cnf(c_2899,plain,
    ( k3_xboole_0(k3_subset_1(sK5,sK6),sK6) = k3_subset_1(sK5,sK6)
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_2307,c_2273])).

cnf(c_2902,plain,
    ( k3_xboole_0(sK6,k3_subset_1(sK5,sK6)) = k3_subset_1(sK5,sK6)
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_0,c_2899])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2282,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4040,plain,
    ( sK6 = sK5
    | r2_hidden(X0,k3_subset_1(sK5,sK6)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2902,c_2282])).

cnf(c_5068,plain,
    ( sK6 = sK5
    | r2_hidden(X0,k5_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4923,c_4040])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2277,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7074,plain,
    ( r2_hidden(X0,k5_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4777,c_2277])).

cnf(c_7387,plain,
    ( r2_hidden(X0,k5_xboole_0(sK5,sK6)) != iProver_top
    | sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5068,c_7074])).

cnf(c_7388,plain,
    ( sK6 = sK5
    | r2_hidden(X0,k5_xboole_0(sK5,sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7387])).

cnf(c_8137,plain,
    ( k5_xboole_0(sK5,sK6) = X0
    | sK6 = sK5
    | r2_hidden(sK3(k5_xboole_0(sK5,sK6),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2274,c_7388])).

cnf(c_20,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_16,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_7073,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_2277])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2276,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5588,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_2276])).

cnf(c_7240,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7073,c_5588])).

cnf(c_7249,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_7240])).

cnf(c_8786,plain,
    ( k5_xboole_0(sK5,sK6) = k1_xboole_0
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_8137,c_7249])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_536,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_36])).

cnf(c_537,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,sK6)) = sK6
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_2519,plain,
    ( k3_subset_1(sK5,k3_subset_1(sK5,sK6)) = sK6 ),
    inference(equality_resolution,[status(thm)],[c_537])).

cnf(c_5077,plain,
    ( k3_subset_1(sK5,k5_xboole_0(sK5,sK6)) = sK6 ),
    inference(demodulation,[status(thm)],[c_4923,c_2519])).

cnf(c_9796,plain,
    ( k3_subset_1(sK5,k1_xboole_0) = sK6
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_8786,c_5077])).

cnf(c_9799,plain,
    ( sK6 = sK5 ),
    inference(demodulation,[status(thm)],[c_9796,c_29])).

cnf(c_1636,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2585,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK5,sK6),sK6)
    | k3_subset_1(sK5,sK6) != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_7808,plain,
    ( r1_tarski(k3_subset_1(sK5,sK6),sK6)
    | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
    | k3_subset_1(sK5,sK6) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | sK6 != X2 ),
    inference(instantiation,[status(thm)],[c_2585])).

cnf(c_7810,plain,
    ( r1_tarski(k3_subset_1(sK5,sK6),sK6)
    | ~ r1_tarski(k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)),sK6)
    | k3_subset_1(sK5,sK6) != k5_xboole_0(sK6,k3_xboole_0(sK6,sK6))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_7808])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2289,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7068,plain,
    ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2289,c_2277])).

cnf(c_7122,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1)
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7068])).

cnf(c_7124,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)),sK6),sK6)
    | r1_tarski(k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_7122])).

cnf(c_5584,plain,
    ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2289,c_2276])).

cnf(c_5617,plain,
    ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0)
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5584])).

cnf(c_5619,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)),sK6),sK6)
    | r1_tarski(k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_5617])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2290,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5375,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2289,c_2290])).

cnf(c_5384,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5375])).

cnf(c_1640,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_5257,plain,
    ( X0 != sK6
    | X1 != sK5
    | k3_subset_1(X1,X0) = k3_subset_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_5259,plain,
    ( k3_subset_1(sK6,sK6) = k3_subset_1(sK5,sK6)
    | sK6 != sK6
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_5257])).

cnf(c_3898,plain,
    ( X0 != k3_subset_1(sK5,sK6)
    | k3_subset_1(sK5,sK6) = X0
    | k3_subset_1(sK5,sK6) != k3_subset_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_2806])).

cnf(c_5256,plain,
    ( k3_subset_1(X0,X1) != k3_subset_1(sK5,sK6)
    | k3_subset_1(sK5,sK6) = k3_subset_1(X0,X1)
    | k3_subset_1(sK5,sK6) != k3_subset_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3898])).

cnf(c_5258,plain,
    ( k3_subset_1(sK6,sK6) != k3_subset_1(sK5,sK6)
    | k3_subset_1(sK5,sK6) = k3_subset_1(sK6,sK6)
    | k3_subset_1(sK5,sK6) != k3_subset_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_5256])).

cnf(c_1633,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2803,plain,
    ( k3_subset_1(sK5,sK6) = k3_subset_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_34,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK5,sK6),sK6)
    | k3_subset_1(sK5,k1_xboole_0) != sK6 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2268,plain,
    ( k3_subset_1(sK5,k1_xboole_0) != sK6
    | r1_tarski(k3_subset_1(sK5,sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2349,plain,
    ( sK6 != sK5
    | r1_tarski(k3_subset_1(sK5,sK6),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2268,c_29])).

cnf(c_2472,plain,
    ( ~ r1_tarski(k3_subset_1(sK5,sK6),sK6)
    | sK6 != sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2349])).

cnf(c_1647,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_27,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_465,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_466,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_476,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_466,c_31])).

cnf(c_23,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1013,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_1014,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_1013])).

cnf(c_1084,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_476,c_1014])).

cnf(c_1119,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1084])).

cnf(c_1121,plain,
    ( k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)) = k3_subset_1(sK6,sK6)
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10834,c_9799,c_7810,c_7124,c_5619,c_5384,c_5259,c_5258,c_2803,c_2472,c_1647,c_1121])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.32/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.99  
% 3.32/0.99  ------  iProver source info
% 3.32/0.99  
% 3.32/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.99  git: non_committed_changes: false
% 3.32/0.99  git: last_make_outside_of_git: false
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    --mode clausify
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         false
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     num_symb
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       true
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     false
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   []
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_full_bw                           [BwDemod]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  ------ Parsing...
% 3.32/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.99  ------ Proving...
% 3.32/0.99  ------ Problem Properties 
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  clauses                                 36
% 3.32/0.99  conjectures                             2
% 3.32/0.99  EPR                                     1
% 3.32/0.99  Horn                                    26
% 3.32/0.99  unary                                   6
% 3.32/0.99  binary                                  17
% 3.32/0.99  lits                                    81
% 3.32/0.99  lits eq                                 27
% 3.32/0.99  fd_pure                                 0
% 3.32/0.99  fd_pseudo                               0
% 3.32/0.99  fd_cond                                 0
% 3.32/0.99  fd_pseudo_cond                          10
% 3.32/0.99  AC symbols                              0
% 3.32/0.99  
% 3.32/0.99  ------ Schedule dynamic 5 is on 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  Current options:
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    --mode clausify
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         false
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     none
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       false
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     false
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   []
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_full_bw                           [BwDemod]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ Proving...
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  % SZS status Theorem for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  fof(f6,axiom,(
% 3.32/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f23,plain,(
% 3.32/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f6])).
% 3.32/0.99  
% 3.32/0.99  fof(f43,plain,(
% 3.32/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.32/0.99    inference(nnf_transformation,[],[f23])).
% 3.32/0.99  
% 3.32/0.99  fof(f44,plain,(
% 3.32/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f45,plain,(
% 3.32/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 3.32/0.99  
% 3.32/0.99  fof(f72,plain,(
% 3.32/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f45])).
% 3.32/0.99  
% 3.32/0.99  fof(f1,axiom,(
% 3.32/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f55,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f1])).
% 3.32/0.99  
% 3.32/0.99  fof(f11,axiom,(
% 3.32/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f25,plain,(
% 3.32/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f11])).
% 3.32/0.99  
% 3.32/0.99  fof(f50,plain,(
% 3.32/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.32/0.99    inference(nnf_transformation,[],[f25])).
% 3.32/0.99  
% 3.32/0.99  fof(f81,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f19,conjecture,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f20,negated_conjecture,(
% 3.32/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.32/0.99    inference(negated_conjecture,[],[f19])).
% 3.32/0.99  
% 3.32/0.99  fof(f28,plain,(
% 3.32/0.99    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f20])).
% 3.32/0.99  
% 3.32/0.99  fof(f51,plain,(
% 3.32/0.99    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/0.99    inference(nnf_transformation,[],[f28])).
% 3.32/0.99  
% 3.32/0.99  fof(f52,plain,(
% 3.32/0.99    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/0.99    inference(flattening,[],[f51])).
% 3.32/0.99  
% 3.32/0.99  fof(f53,plain,(
% 3.32/0.99    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK5) != sK6 | ~r1_tarski(k3_subset_1(sK5,sK6),sK6)) & (k2_subset_1(sK5) = sK6 | r1_tarski(k3_subset_1(sK5,sK6),sK6)) & m1_subset_1(sK6,k1_zfmisc_1(sK5)))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f54,plain,(
% 3.32/0.99    (k2_subset_1(sK5) != sK6 | ~r1_tarski(k3_subset_1(sK5,sK6),sK6)) & (k2_subset_1(sK5) = sK6 | r1_tarski(k3_subset_1(sK5,sK6),sK6)) & m1_subset_1(sK6,k1_zfmisc_1(sK5))),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f52,f53])).
% 3.32/0.99  
% 3.32/0.99  fof(f92,plain,(
% 3.32/0.99    m1_subset_1(sK6,k1_zfmisc_1(sK5))),
% 3.32/0.99    inference(cnf_transformation,[],[f54])).
% 3.32/0.99  
% 3.32/0.99  fof(f15,axiom,(
% 3.32/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f88,plain,(
% 3.32/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f15])).
% 3.32/0.99  
% 3.32/0.99  fof(f10,axiom,(
% 3.32/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f46,plain,(
% 3.32/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f10])).
% 3.32/0.99  
% 3.32/0.99  fof(f47,plain,(
% 3.32/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.32/0.99    inference(rectify,[],[f46])).
% 3.32/0.99  
% 3.32/0.99  fof(f48,plain,(
% 3.32/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f49,plain,(
% 3.32/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).
% 3.32/0.99  
% 3.32/0.99  fof(f77,plain,(
% 3.32/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.32/0.99    inference(cnf_transformation,[],[f49])).
% 3.32/0.99  
% 3.32/0.99  fof(f113,plain,(
% 3.32/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.32/0.99    inference(equality_resolution,[],[f77])).
% 3.32/0.99  
% 3.32/0.99  fof(f8,axiom,(
% 3.32/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f24,plain,(
% 3.32/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f8])).
% 3.32/0.99  
% 3.32/0.99  fof(f75,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f24])).
% 3.32/0.99  
% 3.32/0.99  fof(f14,axiom,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f26,plain,(
% 3.32/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f14])).
% 3.32/0.99  
% 3.32/0.99  fof(f87,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f26])).
% 3.32/0.99  
% 3.32/0.99  fof(f7,axiom,(
% 3.32/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f74,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f7])).
% 3.32/0.99  
% 3.32/0.99  fof(f103,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.32/0.99    inference(definition_unfolding,[],[f87,f74])).
% 3.32/0.99  
% 3.32/0.99  fof(f93,plain,(
% 3.32/0.99    k2_subset_1(sK5) = sK6 | r1_tarski(k3_subset_1(sK5,sK6),sK6)),
% 3.32/0.99    inference(cnf_transformation,[],[f54])).
% 3.32/0.99  
% 3.32/0.99  fof(f17,axiom,(
% 3.32/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f90,plain,(
% 3.32/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f17])).
% 3.32/0.99  
% 3.32/0.99  fof(f12,axiom,(
% 3.32/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f85,plain,(
% 3.32/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f12])).
% 3.32/0.99  
% 3.32/0.99  fof(f95,plain,(
% 3.32/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.32/0.99    inference(definition_unfolding,[],[f90,f85])).
% 3.32/0.99  
% 3.32/0.99  fof(f105,plain,(
% 3.32/0.99    k3_subset_1(sK5,k1_xboole_0) = sK6 | r1_tarski(k3_subset_1(sK5,sK6),sK6)),
% 3.32/0.99    inference(definition_unfolding,[],[f93,f95])).
% 3.32/0.99  
% 3.32/0.99  fof(f13,axiom,(
% 3.32/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f86,plain,(
% 3.32/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.32/0.99    inference(cnf_transformation,[],[f13])).
% 3.32/0.99  
% 3.32/0.99  fof(f102,plain,(
% 3.32/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.32/0.99    inference(definition_unfolding,[],[f86,f95])).
% 3.32/0.99  
% 3.32/0.99  fof(f3,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f33,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.32/0.99    inference(nnf_transformation,[],[f3])).
% 3.32/0.99  
% 3.32/0.99  fof(f34,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.32/0.99    inference(flattening,[],[f33])).
% 3.32/0.99  
% 3.32/0.99  fof(f35,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.32/0.99    inference(rectify,[],[f34])).
% 3.32/0.99  
% 3.32/0.99  fof(f36,plain,(
% 3.32/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f37,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.32/0.99  
% 3.32/0.99  fof(f59,plain,(
% 3.32/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.32/0.99    inference(cnf_transformation,[],[f37])).
% 3.32/0.99  
% 3.32/0.99  fof(f108,plain,(
% 3.32/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.32/0.99    inference(equality_resolution,[],[f59])).
% 3.32/0.99  
% 3.32/0.99  fof(f4,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f38,plain,(
% 3.32/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.32/1.00    inference(nnf_transformation,[],[f4])).
% 3.32/1.00  
% 3.32/1.00  fof(f39,plain,(
% 3.32/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.32/1.00    inference(flattening,[],[f38])).
% 3.32/1.00  
% 3.32/1.00  fof(f40,plain,(
% 3.32/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.32/1.00    inference(rectify,[],[f39])).
% 3.32/1.00  
% 3.32/1.00  fof(f41,plain,(
% 3.32/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.32/1.00    introduced(choice_axiom,[])).
% 3.32/1.00  
% 3.32/1.00  fof(f42,plain,(
% 3.32/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 3.32/1.00  
% 3.32/1.00  fof(f66,plain,(
% 3.32/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.32/1.00    inference(cnf_transformation,[],[f42])).
% 3.32/1.00  
% 3.32/1.00  fof(f100,plain,(
% 3.32/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.32/1.00    inference(definition_unfolding,[],[f66,f74])).
% 3.32/1.00  
% 3.32/1.00  fof(f110,plain,(
% 3.32/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.32/1.00    inference(equality_resolution,[],[f100])).
% 3.32/1.00  
% 3.32/1.00  fof(f9,axiom,(
% 3.32/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f76,plain,(
% 3.32/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.32/1.00    inference(cnf_transformation,[],[f9])).
% 3.32/1.00  
% 3.32/1.00  fof(f5,axiom,(
% 3.32/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f21,plain,(
% 3.32/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.32/1.00    inference(rectify,[],[f5])).
% 3.32/1.00  
% 3.32/1.00  fof(f71,plain,(
% 3.32/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.32/1.00    inference(cnf_transformation,[],[f21])).
% 3.32/1.00  
% 3.32/1.00  fof(f65,plain,(
% 3.32/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.32/1.00    inference(cnf_transformation,[],[f42])).
% 3.32/1.00  
% 3.32/1.00  fof(f101,plain,(
% 3.32/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.32/1.00    inference(definition_unfolding,[],[f65,f74])).
% 3.32/1.00  
% 3.32/1.00  fof(f111,plain,(
% 3.32/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.32/1.00    inference(equality_resolution,[],[f101])).
% 3.32/1.00  
% 3.32/1.00  fof(f16,axiom,(
% 3.32/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f27,plain,(
% 3.32/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/1.00    inference(ennf_transformation,[],[f16])).
% 3.32/1.00  
% 3.32/1.00  fof(f89,plain,(
% 3.32/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.32/1.00    inference(cnf_transformation,[],[f27])).
% 3.32/1.00  
% 3.32/1.00  fof(f2,axiom,(
% 3.32/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f22,plain,(
% 3.32/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.32/1.00    inference(ennf_transformation,[],[f2])).
% 3.32/1.00  
% 3.32/1.00  fof(f29,plain,(
% 3.32/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.32/1.00    inference(nnf_transformation,[],[f22])).
% 3.32/1.00  
% 3.32/1.00  fof(f30,plain,(
% 3.32/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.32/1.00    inference(rectify,[],[f29])).
% 3.32/1.00  
% 3.32/1.00  fof(f31,plain,(
% 3.32/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.32/1.00    introduced(choice_axiom,[])).
% 3.32/1.00  
% 3.32/1.00  fof(f32,plain,(
% 3.32/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.32/1.00  
% 3.32/1.00  fof(f57,plain,(
% 3.32/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f32])).
% 3.32/1.00  
% 3.32/1.00  fof(f58,plain,(
% 3.32/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f32])).
% 3.32/1.00  
% 3.32/1.00  fof(f94,plain,(
% 3.32/1.00    k2_subset_1(sK5) != sK6 | ~r1_tarski(k3_subset_1(sK5,sK6),sK6)),
% 3.32/1.00    inference(cnf_transformation,[],[f54])).
% 3.32/1.00  
% 3.32/1.00  fof(f104,plain,(
% 3.32/1.00    k3_subset_1(sK5,k1_xboole_0) != sK6 | ~r1_tarski(k3_subset_1(sK5,sK6),sK6)),
% 3.32/1.00    inference(definition_unfolding,[],[f94,f95])).
% 3.32/1.00  
% 3.32/1.00  fof(f82,plain,(
% 3.32/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f50])).
% 3.32/1.00  
% 3.32/1.00  fof(f78,plain,(
% 3.32/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.32/1.00    inference(cnf_transformation,[],[f49])).
% 3.32/1.00  
% 3.32/1.00  fof(f112,plain,(
% 3.32/1.00    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.32/1.00    inference(equality_resolution,[],[f78])).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1634,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2806,plain,
% 3.32/1.00      ( X0 != X1
% 3.32/1.00      | k3_subset_1(sK5,sK6) != X1
% 3.32/1.00      | k3_subset_1(sK5,sK6) = X0 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1634]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4803,plain,
% 3.32/1.00      ( X0 != k3_subset_1(X1,X2)
% 3.32/1.00      | k3_subset_1(sK5,sK6) = X0
% 3.32/1.00      | k3_subset_1(sK5,sK6) != k3_subset_1(X1,X2) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_2806]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_10833,plain,
% 3.32/1.00      ( k3_subset_1(sK5,sK6) != k3_subset_1(X0,X1)
% 3.32/1.00      | k3_subset_1(sK5,sK6) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 3.32/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k3_subset_1(X0,X1) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_4803]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_10834,plain,
% 3.32/1.00      ( k3_subset_1(sK5,sK6) != k3_subset_1(sK6,sK6)
% 3.32/1.00      | k3_subset_1(sK5,sK6) = k5_xboole_0(sK6,k3_xboole_0(sK6,sK6))
% 3.32/1.00      | k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)) != k3_subset_1(sK6,sK6) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_10833]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_18,plain,
% 3.32/1.00      ( r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X1 = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2274,plain,
% 3.32/1.00      ( X0 = X1
% 3.32/1.00      | r2_hidden(sK3(X1,X0),X0) = iProver_top
% 3.32/1.00      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_0,plain,
% 3.32/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_28,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_36,negated_conjecture,
% 3.32/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_505,plain,
% 3.32/1.00      ( r2_hidden(X0,X1)
% 3.32/1.00      | v1_xboole_0(X1)
% 3.32/1.00      | k1_zfmisc_1(sK5) != X1
% 3.32/1.00      | sK6 != X0 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_36]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_506,plain,
% 3.32/1.00      ( r2_hidden(sK6,k1_zfmisc_1(sK5)) | v1_xboole_0(k1_zfmisc_1(sK5)) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_505]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_31,plain,
% 3.32/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_512,plain,
% 3.32/1.00      ( r2_hidden(sK6,k1_zfmisc_1(sK5)) ),
% 3.32/1.00      inference(forward_subsumption_resolution,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_506,c_31]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2265,plain,
% 3.32/1.00      ( r2_hidden(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_24,plain,
% 3.32/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2269,plain,
% 3.32/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.32/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3686,plain,
% 3.32/1.00      ( r1_tarski(sK6,sK5) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_2265,c_2269]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_19,plain,
% 3.32/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2273,plain,
% 3.32/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4307,plain,
% 3.32/1.00      ( k3_xboole_0(sK6,sK5) = sK6 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_3686,c_2273]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4777,plain,
% 3.32/1.00      ( k3_xboole_0(sK5,sK6) = sK6 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_0,c_4307]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_30,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_545,plain,
% 3.32/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.32/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5)
% 3.32/1.00      | sK6 != X1 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_36]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_546,plain,
% 3.32/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = k3_subset_1(X0,sK6)
% 3.32/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_545]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2522,plain,
% 3.32/1.00      ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK6)) = k3_subset_1(sK5,sK6) ),
% 3.32/1.00      inference(equality_resolution,[status(thm)],[c_546]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4923,plain,
% 3.32/1.00      ( k3_subset_1(sK5,sK6) = k5_xboole_0(sK5,sK6) ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_4777,c_2522]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_35,negated_conjecture,
% 3.32/1.00      ( r1_tarski(k3_subset_1(sK5,sK6),sK6)
% 3.32/1.00      | k3_subset_1(sK5,k1_xboole_0) = sK6 ),
% 3.32/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2267,plain,
% 3.32/1.00      ( k3_subset_1(sK5,k1_xboole_0) = sK6
% 3.32/1.00      | r1_tarski(k3_subset_1(sK5,sK6),sK6) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_29,plain,
% 3.32/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2307,plain,
% 3.32/1.00      ( sK6 = sK5 | r1_tarski(k3_subset_1(sK5,sK6),sK6) = iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_2267,c_29]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2899,plain,
% 3.32/1.00      ( k3_xboole_0(k3_subset_1(sK5,sK6),sK6) = k3_subset_1(sK5,sK6)
% 3.32/1.00      | sK6 = sK5 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_2307,c_2273]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2902,plain,
% 3.32/1.00      ( k3_xboole_0(sK6,k3_subset_1(sK5,sK6)) = k3_subset_1(sK5,sK6)
% 3.32/1.00      | sK6 = sK5 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_0,c_2899]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_9,plain,
% 3.32/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2282,plain,
% 3.32/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.32/1.00      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4040,plain,
% 3.32/1.00      ( sK6 = sK5
% 3.32/1.00      | r2_hidden(X0,k3_subset_1(sK5,sK6)) != iProver_top
% 3.32/1.00      | r2_hidden(X0,sK6) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_2902,c_2282]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5068,plain,
% 3.32/1.00      ( sK6 = sK5
% 3.32/1.00      | r2_hidden(X0,k5_xboole_0(sK5,sK6)) != iProver_top
% 3.32/1.00      | r2_hidden(X0,sK6) = iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_4923,c_4040]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_14,plain,
% 3.32/1.00      ( ~ r2_hidden(X0,X1)
% 3.32/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.32/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2277,plain,
% 3.32/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.32/1.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7074,plain,
% 3.32/1.00      ( r2_hidden(X0,k5_xboole_0(sK5,sK6)) != iProver_top
% 3.32/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_4777,c_2277]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7387,plain,
% 3.32/1.00      ( r2_hidden(X0,k5_xboole_0(sK5,sK6)) != iProver_top | sK6 = sK5 ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_5068,c_7074]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7388,plain,
% 3.32/1.00      ( sK6 = sK5 | r2_hidden(X0,k5_xboole_0(sK5,sK6)) != iProver_top ),
% 3.32/1.00      inference(renaming,[status(thm)],[c_7387]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8137,plain,
% 3.32/1.00      ( k5_xboole_0(sK5,sK6) = X0
% 3.32/1.00      | sK6 = sK5
% 3.32/1.00      | r2_hidden(sK3(k5_xboole_0(sK5,sK6),X0),X0) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_2274,c_7388]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_20,plain,
% 3.32/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_16,plain,
% 3.32/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7073,plain,
% 3.32/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.32/1.00      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_16,c_2277]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_15,plain,
% 3.32/1.00      ( r2_hidden(X0,X1)
% 3.32/1.00      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.32/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2276,plain,
% 3.32/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.32/1.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5588,plain,
% 3.32/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.32/1.00      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_16,c_2276]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7240,plain,
% 3.32/1.00      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_7073,c_5588]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7249,plain,
% 3.32/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_20,c_7240]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8786,plain,
% 3.32/1.00      ( k5_xboole_0(sK5,sK6) = k1_xboole_0 | sK6 = sK5 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_8137,c_7249]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_32,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_536,plain,
% 3.32/1.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.32/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5)
% 3.32/1.00      | sK6 != X1 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_36]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_537,plain,
% 3.32/1.00      ( k3_subset_1(X0,k3_subset_1(X0,sK6)) = sK6
% 3.32/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK5) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_536]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2519,plain,
% 3.32/1.00      ( k3_subset_1(sK5,k3_subset_1(sK5,sK6)) = sK6 ),
% 3.32/1.00      inference(equality_resolution,[status(thm)],[c_537]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5077,plain,
% 3.32/1.00      ( k3_subset_1(sK5,k5_xboole_0(sK5,sK6)) = sK6 ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_4923,c_2519]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_9796,plain,
% 3.32/1.00      ( k3_subset_1(sK5,k1_xboole_0) = sK6 | sK6 = sK5 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_8786,c_5077]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_9799,plain,
% 3.32/1.00      ( sK6 = sK5 ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_9796,c_29]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1636,plain,
% 3.32/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.32/1.00      theory(equality) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2585,plain,
% 3.32/1.00      ( ~ r1_tarski(X0,X1)
% 3.32/1.00      | r1_tarski(k3_subset_1(sK5,sK6),sK6)
% 3.32/1.00      | k3_subset_1(sK5,sK6) != X0
% 3.32/1.00      | sK6 != X1 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1636]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7808,plain,
% 3.32/1.00      ( r1_tarski(k3_subset_1(sK5,sK6),sK6)
% 3.32/1.00      | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
% 3.32/1.00      | k3_subset_1(sK5,sK6) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 3.32/1.00      | sK6 != X2 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_2585]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7810,plain,
% 3.32/1.00      ( r1_tarski(k3_subset_1(sK5,sK6),sK6)
% 3.32/1.00      | ~ r1_tarski(k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)),sK6)
% 3.32/1.00      | k3_subset_1(sK5,sK6) != k5_xboole_0(sK6,k3_xboole_0(sK6,sK6))
% 3.32/1.00      | sK6 != sK6 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_7808]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2,plain,
% 3.32/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2289,plain,
% 3.32/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.32/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7068,plain,
% 3.32/1.00      ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1) != iProver_top
% 3.32/1.00      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_2289,c_2277]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7122,plain,
% 3.32/1.00      ( ~ r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1)
% 3.32/1.00      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 3.32/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7068]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7124,plain,
% 3.32/1.00      ( ~ r2_hidden(sK0(k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)),sK6),sK6)
% 3.32/1.00      | r1_tarski(k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)),sK6) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_7122]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5584,plain,
% 3.32/1.00      ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
% 3.32/1.00      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_2289,c_2276]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5617,plain,
% 3.32/1.00      ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0)
% 3.32/1.00      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 3.32/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5584]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5619,plain,
% 3.32/1.00      ( r2_hidden(sK0(k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)),sK6),sK6)
% 3.32/1.00      | r1_tarski(k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)),sK6) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_5617]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1,plain,
% 3.32/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2290,plain,
% 3.32/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.32/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5375,plain,
% 3.32/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_2289,c_2290]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5384,plain,
% 3.32/1.00      ( r1_tarski(sK6,sK6) = iProver_top ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_5375]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1640,plain,
% 3.32/1.00      ( X0 != X1 | X2 != X3 | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
% 3.32/1.00      theory(equality) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5257,plain,
% 3.32/1.00      ( X0 != sK6
% 3.32/1.00      | X1 != sK5
% 3.32/1.00      | k3_subset_1(X1,X0) = k3_subset_1(sK5,sK6) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1640]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5259,plain,
% 3.32/1.00      ( k3_subset_1(sK6,sK6) = k3_subset_1(sK5,sK6)
% 3.32/1.00      | sK6 != sK6
% 3.32/1.00      | sK6 != sK5 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_5257]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3898,plain,
% 3.32/1.00      ( X0 != k3_subset_1(sK5,sK6)
% 3.32/1.00      | k3_subset_1(sK5,sK6) = X0
% 3.32/1.00      | k3_subset_1(sK5,sK6) != k3_subset_1(sK5,sK6) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_2806]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5256,plain,
% 3.32/1.00      ( k3_subset_1(X0,X1) != k3_subset_1(sK5,sK6)
% 3.32/1.00      | k3_subset_1(sK5,sK6) = k3_subset_1(X0,X1)
% 3.32/1.00      | k3_subset_1(sK5,sK6) != k3_subset_1(sK5,sK6) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_3898]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5258,plain,
% 3.32/1.00      ( k3_subset_1(sK6,sK6) != k3_subset_1(sK5,sK6)
% 3.32/1.00      | k3_subset_1(sK5,sK6) = k3_subset_1(sK6,sK6)
% 3.32/1.00      | k3_subset_1(sK5,sK6) != k3_subset_1(sK5,sK6) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_5256]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1633,plain,( X0 = X0 ),theory(equality) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2803,plain,
% 3.32/1.00      ( k3_subset_1(sK5,sK6) = k3_subset_1(sK5,sK6) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1633]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_34,negated_conjecture,
% 3.32/1.00      ( ~ r1_tarski(k3_subset_1(sK5,sK6),sK6)
% 3.32/1.00      | k3_subset_1(sK5,k1_xboole_0) != sK6 ),
% 3.32/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2268,plain,
% 3.32/1.00      ( k3_subset_1(sK5,k1_xboole_0) != sK6
% 3.32/1.00      | r1_tarski(k3_subset_1(sK5,sK6),sK6) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2349,plain,
% 3.32/1.00      ( sK6 != sK5 | r1_tarski(k3_subset_1(sK5,sK6),sK6) != iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_2268,c_29]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2472,plain,
% 3.32/1.00      ( ~ r1_tarski(k3_subset_1(sK5,sK6),sK6) | sK6 != sK5 ),
% 3.32/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2349]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1647,plain,
% 3.32/1.00      ( sK6 = sK6 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1633]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_27,plain,
% 3.32/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_465,plain,
% 3.32/1.00      ( ~ r2_hidden(X0,X1)
% 3.32/1.00      | v1_xboole_0(X1)
% 3.32/1.00      | X2 != X0
% 3.32/1.00      | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
% 3.32/1.00      | k1_zfmisc_1(X3) != X1 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_466,plain,
% 3.32/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.32/1.00      | v1_xboole_0(k1_zfmisc_1(X1))
% 3.32/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_465]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_476,plain,
% 3.32/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.32/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.32/1.00      inference(forward_subsumption_resolution,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_466,c_31]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_23,plain,
% 3.32/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1013,plain,
% 3.32/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.32/1.00      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1014,plain,
% 3.32/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.32/1.00      inference(renaming,[status(thm)],[c_1013]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1084,plain,
% 3.32/1.00      ( ~ r1_tarski(X0,X1)
% 3.32/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.32/1.00      inference(bin_hyper_res,[status(thm)],[c_476,c_1014]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1119,plain,
% 3.32/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.32/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1084]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1121,plain,
% 3.32/1.00      ( k5_xboole_0(sK6,k3_xboole_0(sK6,sK6)) = k3_subset_1(sK6,sK6)
% 3.32/1.00      | r1_tarski(sK6,sK6) != iProver_top ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1119]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(contradiction,plain,
% 3.32/1.00      ( $false ),
% 3.32/1.00      inference(minisat,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_10834,c_9799,c_7810,c_7124,c_5619,c_5384,c_5259,
% 3.32/1.00                 c_5258,c_2803,c_2472,c_1647,c_1121]) ).
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/1.00  
% 3.32/1.00  ------                               Statistics
% 3.32/1.00  
% 3.32/1.00  ------ General
% 3.32/1.00  
% 3.32/1.00  abstr_ref_over_cycles:                  0
% 3.32/1.00  abstr_ref_under_cycles:                 0
% 3.32/1.00  gc_basic_clause_elim:                   0
% 3.32/1.00  forced_gc_time:                         0
% 3.32/1.00  parsing_time:                           0.013
% 3.32/1.00  unif_index_cands_time:                  0.
% 3.32/1.00  unif_index_add_time:                    0.
% 3.32/1.00  orderings_time:                         0.
% 3.32/1.00  out_proof_time:                         0.011
% 3.32/1.00  total_time:                             0.284
% 3.32/1.00  num_of_symbols:                         47
% 3.32/1.00  num_of_terms:                           11378
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing
% 3.32/1.00  
% 3.32/1.00  num_of_splits:                          0
% 3.32/1.00  num_of_split_atoms:                     0
% 3.32/1.00  num_of_reused_defs:                     0
% 3.32/1.00  num_eq_ax_congr_red:                    43
% 3.32/1.00  num_of_sem_filtered_clauses:            1
% 3.32/1.00  num_of_subtypes:                        0
% 3.32/1.00  monotx_restored_types:                  0
% 3.32/1.00  sat_num_of_epr_types:                   0
% 3.32/1.00  sat_num_of_non_cyclic_types:            0
% 3.32/1.00  sat_guarded_non_collapsed_types:        0
% 3.32/1.00  num_pure_diseq_elim:                    0
% 3.32/1.00  simp_replaced_by:                       0
% 3.32/1.00  res_preprocessed:                       162
% 3.32/1.00  prep_upred:                             0
% 3.32/1.00  prep_unflattend:                        92
% 3.32/1.00  smt_new_axioms:                         0
% 3.32/1.00  pred_elim_cands:                        2
% 3.32/1.00  pred_elim:                              2
% 3.32/1.00  pred_elim_cl:                           1
% 3.32/1.00  pred_elim_cycles:                       4
% 3.32/1.00  merged_defs:                            16
% 3.32/1.00  merged_defs_ncl:                        0
% 3.32/1.00  bin_hyper_res:                          18
% 3.32/1.00  prep_cycles:                            4
% 3.32/1.00  pred_elim_time:                         0.014
% 3.32/1.00  splitting_time:                         0.
% 3.32/1.00  sem_filter_time:                        0.
% 3.32/1.00  monotx_time:                            0.001
% 3.32/1.00  subtype_inf_time:                       0.
% 3.32/1.00  
% 3.32/1.00  ------ Problem properties
% 3.32/1.00  
% 3.32/1.00  clauses:                                36
% 3.32/1.00  conjectures:                            2
% 3.32/1.00  epr:                                    1
% 3.32/1.00  horn:                                   26
% 3.32/1.00  ground:                                 3
% 3.32/1.00  unary:                                  6
% 3.32/1.00  binary:                                 17
% 3.32/1.00  lits:                                   81
% 3.32/1.00  lits_eq:                                27
% 3.32/1.00  fd_pure:                                0
% 3.32/1.00  fd_pseudo:                              0
% 3.32/1.00  fd_cond:                                0
% 3.32/1.00  fd_pseudo_cond:                         10
% 3.32/1.00  ac_symbols:                             0
% 3.32/1.00  
% 3.32/1.00  ------ Propositional Solver
% 3.32/1.00  
% 3.32/1.00  prop_solver_calls:                      27
% 3.32/1.00  prop_fast_solver_calls:                 1071
% 3.32/1.00  smt_solver_calls:                       0
% 3.32/1.00  smt_fast_solver_calls:                  0
% 3.32/1.00  prop_num_of_clauses:                    3683
% 3.32/1.00  prop_preprocess_simplified:             11358
% 3.32/1.00  prop_fo_subsumed:                       5
% 3.32/1.00  prop_solver_time:                       0.
% 3.32/1.00  smt_solver_time:                        0.
% 3.32/1.00  smt_fast_solver_time:                   0.
% 3.32/1.00  prop_fast_solver_time:                  0.
% 3.32/1.00  prop_unsat_core_time:                   0.
% 3.32/1.00  
% 3.32/1.00  ------ QBF
% 3.32/1.00  
% 3.32/1.00  qbf_q_res:                              0
% 3.32/1.00  qbf_num_tautologies:                    0
% 3.32/1.00  qbf_prep_cycles:                        0
% 3.32/1.00  
% 3.32/1.00  ------ BMC1
% 3.32/1.00  
% 3.32/1.00  bmc1_current_bound:                     -1
% 3.32/1.00  bmc1_last_solved_bound:                 -1
% 3.32/1.00  bmc1_unsat_core_size:                   -1
% 3.32/1.00  bmc1_unsat_core_parents_size:           -1
% 3.32/1.00  bmc1_merge_next_fun:                    0
% 3.32/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.32/1.00  
% 3.32/1.00  ------ Instantiation
% 3.32/1.00  
% 3.32/1.00  inst_num_of_clauses:                    941
% 3.32/1.00  inst_num_in_passive:                    435
% 3.32/1.00  inst_num_in_active:                     329
% 3.32/1.00  inst_num_in_unprocessed:                176
% 3.32/1.00  inst_num_of_loops:                      369
% 3.32/1.00  inst_num_of_learning_restarts:          0
% 3.32/1.00  inst_num_moves_active_passive:          38
% 3.32/1.00  inst_lit_activity:                      0
% 3.32/1.00  inst_lit_activity_moves:                0
% 3.32/1.00  inst_num_tautologies:                   0
% 3.32/1.00  inst_num_prop_implied:                  0
% 3.32/1.00  inst_num_existing_simplified:           0
% 3.32/1.00  inst_num_eq_res_simplified:             0
% 3.32/1.00  inst_num_child_elim:                    0
% 3.32/1.00  inst_num_of_dismatching_blockings:      842
% 3.32/1.00  inst_num_of_non_proper_insts:           948
% 3.32/1.00  inst_num_of_duplicates:                 0
% 3.32/1.00  inst_inst_num_from_inst_to_res:         0
% 3.32/1.00  inst_dismatching_checking_time:         0.
% 3.32/1.00  
% 3.32/1.00  ------ Resolution
% 3.32/1.00  
% 3.32/1.00  res_num_of_clauses:                     0
% 3.32/1.00  res_num_in_passive:                     0
% 3.32/1.00  res_num_in_active:                      0
% 3.32/1.00  res_num_of_loops:                       166
% 3.32/1.00  res_forward_subset_subsumed:            24
% 3.32/1.00  res_backward_subset_subsumed:           0
% 3.32/1.00  res_forward_subsumed:                   3
% 3.32/1.00  res_backward_subsumed:                  0
% 3.32/1.00  res_forward_subsumption_resolution:     3
% 3.32/1.00  res_backward_subsumption_resolution:    0
% 3.32/1.00  res_clause_to_clause_subsumption:       842
% 3.32/1.00  res_orphan_elimination:                 0
% 3.32/1.00  res_tautology_del:                      46
% 3.32/1.00  res_num_eq_res_simplified:              0
% 3.32/1.00  res_num_sel_changes:                    0
% 3.32/1.00  res_moves_from_active_to_pass:          0
% 3.32/1.00  
% 3.32/1.00  ------ Superposition
% 3.32/1.00  
% 3.32/1.00  sup_time_total:                         0.
% 3.32/1.00  sup_time_generating:                    0.
% 3.32/1.00  sup_time_sim_full:                      0.
% 3.32/1.00  sup_time_sim_immed:                     0.
% 3.32/1.00  
% 3.32/1.00  sup_num_of_clauses:                     152
% 3.32/1.00  sup_num_in_active:                      33
% 3.32/1.00  sup_num_in_passive:                     119
% 3.32/1.00  sup_num_of_loops:                       72
% 3.32/1.00  sup_fw_superposition:                   107
% 3.32/1.00  sup_bw_superposition:                   137
% 3.32/1.00  sup_immediate_simplified:               33
% 3.32/1.00  sup_given_eliminated:                   1
% 3.32/1.00  comparisons_done:                       0
% 3.32/1.00  comparisons_avoided:                    48
% 3.32/1.00  
% 3.32/1.00  ------ Simplifications
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  sim_fw_subset_subsumed:                 16
% 3.32/1.00  sim_bw_subset_subsumed:                 16
% 3.32/1.00  sim_fw_subsumed:                        7
% 3.32/1.00  sim_bw_subsumed:                        2
% 3.32/1.00  sim_fw_subsumption_res:                 0
% 3.32/1.00  sim_bw_subsumption_res:                 0
% 3.32/1.00  sim_tautology_del:                      26
% 3.32/1.00  sim_eq_tautology_del:                   15
% 3.32/1.00  sim_eq_res_simp:                        1
% 3.32/1.00  sim_fw_demodulated:                     5
% 3.32/1.00  sim_bw_demodulated:                     31
% 3.32/1.00  sim_light_normalised:                   6
% 3.32/1.00  sim_joinable_taut:                      0
% 3.32/1.00  sim_joinable_simp:                      0
% 3.32/1.00  sim_ac_normalised:                      0
% 3.32/1.00  sim_smt_subsumption:                    0
% 3.32/1.00  
%------------------------------------------------------------------------------
