%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:26 EST 2020

% Result     : Theorem 11.69s
% Output     : CNFRefutation 11.69s
% Verified   : 
% Statistics : Number of formulae       :  172 (1652 expanded)
%              Number of clauses        :   98 ( 507 expanded)
%              Number of leaves         :   18 ( 329 expanded)
%              Depth                    :   26
%              Number of atoms          :  498 (7580 expanded)
%              Number of equality atoms :  207 (1389 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f27])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X4] :
            ( r2_hidden(X1,X4)
            | ~ r2_hidden(X4,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f49])).

fof(f52,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r2_hidden(X3,X2) )
     => ( ~ r2_hidden(X1,sK7)
        & r2_hidden(sK7,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_hidden(X3,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r2_hidden(X4,X2) )
          | r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & r2_hidden(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ? [X3] :
            ( ~ r2_hidden(sK5,X3)
            & r2_hidden(X3,sK6) )
        | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
      & ( ! [X4] :
            ( r2_hidden(sK5,X4)
            | ~ r2_hidden(X4,sK6) )
        | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
      & r2_hidden(sK5,sK4)
      & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ( ~ r2_hidden(sK5,sK7)
        & r2_hidden(sK7,sK6) )
      | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
    & ( ! [X4] :
          ( r2_hidden(sK5,X4)
          | ~ r2_hidden(X4,sK6) )
      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f50,f52,f51])).

fof(f83,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,
    ( r2_hidden(sK7,sK6)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    ! [X4] :
      ( r2_hidden(sK5,X4)
      | ~ r2_hidden(X4,sK6)
      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,
    ( ~ r2_hidden(sK5,sK7)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f25])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f46])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f43])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f60])).

fof(f89,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f88])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f68])).

fof(f84,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1216,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1211,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3111,plain,
    ( sK1(k1_tarski(X0),X1) = X0
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1211])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1207,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_12497,plain,
    ( sK1(k1_tarski(X0),X1) = X0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3111,c_1207])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1187,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1198,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5175,plain,
    ( k6_setfam_1(sK4,sK6) = k8_setfam_1(sK4,sK6)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1187,c_1198])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1196,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3235,plain,
    ( k6_setfam_1(sK4,sK6) = k1_setfam_1(sK6) ),
    inference(superposition,[status(thm)],[c_1187,c_1196])).

cnf(c_5178,plain,
    ( k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5175,c_3235])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1190,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6141,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK7,sK6) = iProver_top
    | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5178,c_1190])).

cnf(c_12622,plain,
    ( sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
    | sK6 = k1_xboole_0
    | r2_hidden(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_12497,c_6141])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(sK5,X0)
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1189,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK5,X0) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16287,plain,
    ( sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
    | sK6 = k1_xboole_0
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK5,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_12622,c_1189])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1652,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | k4_xboole_0(k1_tarski(sK5),k8_setfam_1(sK4,sK6)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1653,plain,
    ( k4_xboole_0(k1_tarski(sK5),k8_setfam_1(sK4,sK6)) != k1_xboole_0
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1652])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3007,plain,
    ( ~ r2_hidden(sK5,X0)
    | k4_xboole_0(k1_tarski(sK5),X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4775,plain,
    ( ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | k4_xboole_0(k1_tarski(sK5),k8_setfam_1(sK4,sK6)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3007])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | ~ r2_hidden(sK5,sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1191,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6140,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5178,c_1191])).

cnf(c_12623,plain,
    ( sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
    | sK6 = k1_xboole_0
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_12497,c_6140])).

cnf(c_12757,plain,
    ( ~ r2_hidden(sK5,sK7)
    | sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12623])).

cnf(c_16328,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | r2_hidden(sK5,sK7)
    | sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16287])).

cnf(c_16472,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
    | sK6 = k1_xboole_0
    | sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16287,c_1653,c_4775,c_12757,c_16328])).

cnf(c_16473,plain,
    ( sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
    | sK6 = k1_xboole_0
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_16472])).

cnf(c_1210,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16481,plain,
    ( k4_xboole_0(k1_tarski(sK5),k8_setfam_1(sK4,sK6)) = k1_xboole_0
    | sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16473,c_1210])).

cnf(c_1720,plain,
    ( ~ r2_hidden(sK7,sK6)
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | r2_hidden(sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_6216,plain,
    ( ~ r2_hidden(sK5,k1_setfam_1(sK6))
    | ~ r2_hidden(sK5,sK7)
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6140])).

cnf(c_6217,plain,
    ( r2_hidden(sK7,sK6)
    | ~ r2_hidden(sK5,k1_setfam_1(sK6))
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6141])).

cnf(c_28,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1192,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2251,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(X0,k1_setfam_1(sK6)) = iProver_top
    | r2_hidden(sK5,sK3(sK6,X0)) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_1189])).

cnf(c_11,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1208,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,sK3(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1193,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,sK3(X0,X1)) != iProver_top
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5412,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k1_tarski(X1),k1_setfam_1(X0)) = iProver_top
    | r2_hidden(X1,sK3(X0,k1_tarski(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_1193])).

cnf(c_50916,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k1_tarski(sK5),k1_setfam_1(sK6)) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_5412])).

cnf(c_51779,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK5,k1_setfam_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_50916,c_1207])).

cnf(c_51797,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | r2_hidden(sK5,k1_setfam_1(sK6))
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_51779])).

cnf(c_51803,plain,
    ( k4_xboole_0(k1_tarski(sK5),k8_setfam_1(sK4,sK6)) = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16481,c_1720,c_4775,c_6216,c_6217,c_51797])).

cnf(c_1209,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_51808,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_51803,c_1209])).

cnf(c_52320,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_51808,c_1191])).

cnf(c_25,plain,
    ( r1_tarski(k1_setfam_1(X0),X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4012,plain,
    ( r1_tarski(k1_setfam_1(X0),sK7)
    | ~ r2_hidden(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_15221,plain,
    ( r1_tarski(k1_setfam_1(sK6),sK7)
    | ~ r2_hidden(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_4012])).

cnf(c_15222,plain,
    ( r1_tarski(k1_setfam_1(sK6),sK7) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15221])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2006,plain,
    ( ~ r1_tarski(X0,sK7)
    | ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4011,plain,
    ( ~ r1_tarski(k1_setfam_1(X0),sK7)
    | ~ r2_hidden(sK5,k1_setfam_1(X0))
    | r2_hidden(sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_42762,plain,
    ( ~ r1_tarski(k1_setfam_1(sK6),sK7)
    | ~ r2_hidden(sK5,k1_setfam_1(sK6))
    | r2_hidden(sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_4011])).

cnf(c_42763,plain,
    ( r1_tarski(k1_setfam_1(sK6),sK7) != iProver_top
    | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top
    | r2_hidden(sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42762])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1204,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12609,plain,
    ( sK1(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X2))) = X0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_12497,c_1204])).

cnf(c_16779,plain,
    ( sK1(k1_tarski(sK5),k4_xboole_0(k1_setfam_1(sK6),k1_tarski(X0))) = sK5
    | sK6 = k1_xboole_0
    | r2_hidden(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_12609,c_6141])).

cnf(c_39,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_51991,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16779,c_39,c_51808])).

cnf(c_52315,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k1_setfam_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5178,c_51808])).

cnf(c_52750,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_52320,c_15222,c_42763,c_51991,c_52315])).

cnf(c_52986,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_52750,c_1190])).

cnf(c_21,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1199,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1200,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1276,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1199,c_1200])).

cnf(c_52991,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_52986,c_1276])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_48398,plain,
    ( ~ r2_hidden(sK7,X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_48404,plain,
    ( r2_hidden(sK7,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48398])).

cnf(c_48406,plain,
    ( r2_hidden(sK7,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_48404])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1219,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1212,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2929,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1212,c_1210])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1205,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7796,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2929,c_1205])).

cnf(c_7843,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_7796])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52991,c_48406,c_7843,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.69/2.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.69/2.04  
% 11.69/2.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.69/2.04  
% 11.69/2.04  ------  iProver source info
% 11.69/2.04  
% 11.69/2.04  git: date: 2020-06-30 10:37:57 +0100
% 11.69/2.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.69/2.04  git: non_committed_changes: false
% 11.69/2.04  git: last_make_outside_of_git: false
% 11.69/2.04  
% 11.69/2.04  ------ 
% 11.69/2.04  
% 11.69/2.04  ------ Input Options
% 11.69/2.04  
% 11.69/2.04  --out_options                           all
% 11.69/2.04  --tptp_safe_out                         true
% 11.69/2.04  --problem_path                          ""
% 11.69/2.04  --include_path                          ""
% 11.69/2.04  --clausifier                            res/vclausify_rel
% 11.69/2.04  --clausifier_options                    --mode clausify
% 11.69/2.04  --stdin                                 false
% 11.69/2.04  --stats_out                             all
% 11.69/2.04  
% 11.69/2.04  ------ General Options
% 11.69/2.04  
% 11.69/2.04  --fof                                   false
% 11.69/2.04  --time_out_real                         305.
% 11.69/2.04  --time_out_virtual                      -1.
% 11.69/2.04  --symbol_type_check                     false
% 11.69/2.04  --clausify_out                          false
% 11.69/2.04  --sig_cnt_out                           false
% 11.69/2.04  --trig_cnt_out                          false
% 11.69/2.04  --trig_cnt_out_tolerance                1.
% 11.69/2.04  --trig_cnt_out_sk_spl                   false
% 11.69/2.04  --abstr_cl_out                          false
% 11.69/2.04  
% 11.69/2.04  ------ Global Options
% 11.69/2.04  
% 11.69/2.04  --schedule                              default
% 11.69/2.04  --add_important_lit                     false
% 11.69/2.04  --prop_solver_per_cl                    1000
% 11.69/2.04  --min_unsat_core                        false
% 11.69/2.04  --soft_assumptions                      false
% 11.69/2.04  --soft_lemma_size                       3
% 11.69/2.04  --prop_impl_unit_size                   0
% 11.69/2.04  --prop_impl_unit                        []
% 11.69/2.04  --share_sel_clauses                     true
% 11.69/2.04  --reset_solvers                         false
% 11.69/2.04  --bc_imp_inh                            [conj_cone]
% 11.69/2.04  --conj_cone_tolerance                   3.
% 11.69/2.04  --extra_neg_conj                        none
% 11.69/2.04  --large_theory_mode                     true
% 11.69/2.04  --prolific_symb_bound                   200
% 11.69/2.04  --lt_threshold                          2000
% 11.69/2.04  --clause_weak_htbl                      true
% 11.69/2.04  --gc_record_bc_elim                     false
% 11.69/2.04  
% 11.69/2.04  ------ Preprocessing Options
% 11.69/2.04  
% 11.69/2.04  --preprocessing_flag                    true
% 11.69/2.04  --time_out_prep_mult                    0.1
% 11.69/2.04  --splitting_mode                        input
% 11.69/2.04  --splitting_grd                         true
% 11.69/2.04  --splitting_cvd                         false
% 11.69/2.04  --splitting_cvd_svl                     false
% 11.69/2.04  --splitting_nvd                         32
% 11.69/2.04  --sub_typing                            true
% 11.69/2.04  --prep_gs_sim                           true
% 11.69/2.04  --prep_unflatten                        true
% 11.69/2.04  --prep_res_sim                          true
% 11.69/2.04  --prep_upred                            true
% 11.69/2.04  --prep_sem_filter                       exhaustive
% 11.69/2.04  --prep_sem_filter_out                   false
% 11.69/2.04  --pred_elim                             true
% 11.69/2.04  --res_sim_input                         true
% 11.69/2.04  --eq_ax_congr_red                       true
% 11.69/2.04  --pure_diseq_elim                       true
% 11.69/2.04  --brand_transform                       false
% 11.69/2.04  --non_eq_to_eq                          false
% 11.69/2.04  --prep_def_merge                        true
% 11.69/2.04  --prep_def_merge_prop_impl              false
% 11.69/2.04  --prep_def_merge_mbd                    true
% 11.69/2.04  --prep_def_merge_tr_red                 false
% 11.69/2.04  --prep_def_merge_tr_cl                  false
% 11.69/2.04  --smt_preprocessing                     true
% 11.69/2.04  --smt_ac_axioms                         fast
% 11.69/2.04  --preprocessed_out                      false
% 11.69/2.04  --preprocessed_stats                    false
% 11.69/2.04  
% 11.69/2.04  ------ Abstraction refinement Options
% 11.69/2.04  
% 11.69/2.04  --abstr_ref                             []
% 11.69/2.04  --abstr_ref_prep                        false
% 11.69/2.04  --abstr_ref_until_sat                   false
% 11.69/2.04  --abstr_ref_sig_restrict                funpre
% 11.69/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 11.69/2.04  --abstr_ref_under                       []
% 11.69/2.04  
% 11.69/2.04  ------ SAT Options
% 11.69/2.04  
% 11.69/2.04  --sat_mode                              false
% 11.69/2.04  --sat_fm_restart_options                ""
% 11.69/2.04  --sat_gr_def                            false
% 11.69/2.04  --sat_epr_types                         true
% 11.69/2.04  --sat_non_cyclic_types                  false
% 11.69/2.04  --sat_finite_models                     false
% 11.69/2.04  --sat_fm_lemmas                         false
% 11.69/2.04  --sat_fm_prep                           false
% 11.69/2.04  --sat_fm_uc_incr                        true
% 11.69/2.04  --sat_out_model                         small
% 11.69/2.04  --sat_out_clauses                       false
% 11.69/2.04  
% 11.69/2.04  ------ QBF Options
% 11.69/2.04  
% 11.69/2.04  --qbf_mode                              false
% 11.69/2.04  --qbf_elim_univ                         false
% 11.69/2.04  --qbf_dom_inst                          none
% 11.69/2.04  --qbf_dom_pre_inst                      false
% 11.69/2.04  --qbf_sk_in                             false
% 11.69/2.04  --qbf_pred_elim                         true
% 11.69/2.04  --qbf_split                             512
% 11.69/2.04  
% 11.69/2.04  ------ BMC1 Options
% 11.69/2.04  
% 11.69/2.04  --bmc1_incremental                      false
% 11.69/2.04  --bmc1_axioms                           reachable_all
% 11.69/2.04  --bmc1_min_bound                        0
% 11.69/2.04  --bmc1_max_bound                        -1
% 11.69/2.04  --bmc1_max_bound_default                -1
% 11.69/2.04  --bmc1_symbol_reachability              true
% 11.69/2.04  --bmc1_property_lemmas                  false
% 11.69/2.04  --bmc1_k_induction                      false
% 11.69/2.04  --bmc1_non_equiv_states                 false
% 11.69/2.04  --bmc1_deadlock                         false
% 11.69/2.04  --bmc1_ucm                              false
% 11.69/2.04  --bmc1_add_unsat_core                   none
% 11.69/2.04  --bmc1_unsat_core_children              false
% 11.69/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 11.69/2.04  --bmc1_out_stat                         full
% 11.69/2.04  --bmc1_ground_init                      false
% 11.69/2.04  --bmc1_pre_inst_next_state              false
% 11.69/2.04  --bmc1_pre_inst_state                   false
% 11.69/2.04  --bmc1_pre_inst_reach_state             false
% 11.69/2.04  --bmc1_out_unsat_core                   false
% 11.69/2.04  --bmc1_aig_witness_out                  false
% 11.69/2.04  --bmc1_verbose                          false
% 11.69/2.04  --bmc1_dump_clauses_tptp                false
% 11.69/2.04  --bmc1_dump_unsat_core_tptp             false
% 11.69/2.04  --bmc1_dump_file                        -
% 11.69/2.04  --bmc1_ucm_expand_uc_limit              128
% 11.69/2.04  --bmc1_ucm_n_expand_iterations          6
% 11.69/2.04  --bmc1_ucm_extend_mode                  1
% 11.69/2.04  --bmc1_ucm_init_mode                    2
% 11.69/2.04  --bmc1_ucm_cone_mode                    none
% 11.69/2.04  --bmc1_ucm_reduced_relation_type        0
% 11.69/2.04  --bmc1_ucm_relax_model                  4
% 11.69/2.04  --bmc1_ucm_full_tr_after_sat            true
% 11.69/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 11.69/2.04  --bmc1_ucm_layered_model                none
% 11.69/2.04  --bmc1_ucm_max_lemma_size               10
% 11.69/2.04  
% 11.69/2.04  ------ AIG Options
% 11.69/2.04  
% 11.69/2.04  --aig_mode                              false
% 11.69/2.04  
% 11.69/2.04  ------ Instantiation Options
% 11.69/2.04  
% 11.69/2.04  --instantiation_flag                    true
% 11.69/2.04  --inst_sos_flag                         false
% 11.69/2.04  --inst_sos_phase                        true
% 11.69/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.69/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.69/2.04  --inst_lit_sel_side                     num_symb
% 11.69/2.04  --inst_solver_per_active                1400
% 11.69/2.04  --inst_solver_calls_frac                1.
% 11.69/2.04  --inst_passive_queue_type               priority_queues
% 11.69/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.69/2.04  --inst_passive_queues_freq              [25;2]
% 11.69/2.04  --inst_dismatching                      true
% 11.69/2.04  --inst_eager_unprocessed_to_passive     true
% 11.69/2.04  --inst_prop_sim_given                   true
% 11.69/2.04  --inst_prop_sim_new                     false
% 11.69/2.04  --inst_subs_new                         false
% 11.69/2.04  --inst_eq_res_simp                      false
% 11.69/2.04  --inst_subs_given                       false
% 11.69/2.04  --inst_orphan_elimination               true
% 11.69/2.04  --inst_learning_loop_flag               true
% 11.69/2.04  --inst_learning_start                   3000
% 11.69/2.04  --inst_learning_factor                  2
% 11.69/2.04  --inst_start_prop_sim_after_learn       3
% 11.69/2.04  --inst_sel_renew                        solver
% 11.69/2.04  --inst_lit_activity_flag                true
% 11.69/2.04  --inst_restr_to_given                   false
% 11.69/2.04  --inst_activity_threshold               500
% 11.69/2.04  --inst_out_proof                        true
% 11.69/2.04  
% 11.69/2.04  ------ Resolution Options
% 11.69/2.04  
% 11.69/2.04  --resolution_flag                       true
% 11.69/2.04  --res_lit_sel                           adaptive
% 11.69/2.04  --res_lit_sel_side                      none
% 11.69/2.04  --res_ordering                          kbo
% 11.69/2.04  --res_to_prop_solver                    active
% 11.69/2.04  --res_prop_simpl_new                    false
% 11.69/2.04  --res_prop_simpl_given                  true
% 11.69/2.04  --res_passive_queue_type                priority_queues
% 11.69/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.69/2.04  --res_passive_queues_freq               [15;5]
% 11.69/2.04  --res_forward_subs                      full
% 11.69/2.04  --res_backward_subs                     full
% 11.69/2.04  --res_forward_subs_resolution           true
% 11.69/2.04  --res_backward_subs_resolution          true
% 11.69/2.04  --res_orphan_elimination                true
% 11.69/2.04  --res_time_limit                        2.
% 11.69/2.04  --res_out_proof                         true
% 11.69/2.04  
% 11.69/2.04  ------ Superposition Options
% 11.69/2.04  
% 11.69/2.04  --superposition_flag                    true
% 11.69/2.04  --sup_passive_queue_type                priority_queues
% 11.69/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.69/2.04  --sup_passive_queues_freq               [8;1;4]
% 11.69/2.04  --demod_completeness_check              fast
% 11.69/2.04  --demod_use_ground                      true
% 11.69/2.04  --sup_to_prop_solver                    passive
% 11.69/2.04  --sup_prop_simpl_new                    true
% 11.69/2.04  --sup_prop_simpl_given                  true
% 11.69/2.04  --sup_fun_splitting                     false
% 11.69/2.04  --sup_smt_interval                      50000
% 11.69/2.04  
% 11.69/2.04  ------ Superposition Simplification Setup
% 11.69/2.04  
% 11.69/2.04  --sup_indices_passive                   []
% 11.69/2.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.69/2.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.69/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.69/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 11.69/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.69/2.04  --sup_full_bw                           [BwDemod]
% 11.69/2.04  --sup_immed_triv                        [TrivRules]
% 11.69/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.69/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.69/2.04  --sup_immed_bw_main                     []
% 11.69/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.69/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 11.69/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.69/2.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.69/2.04  
% 11.69/2.04  ------ Combination Options
% 11.69/2.04  
% 11.69/2.04  --comb_res_mult                         3
% 11.69/2.04  --comb_sup_mult                         2
% 11.69/2.04  --comb_inst_mult                        10
% 11.69/2.04  
% 11.69/2.04  ------ Debug Options
% 11.69/2.04  
% 11.69/2.04  --dbg_backtrace                         false
% 11.69/2.04  --dbg_dump_prop_clauses                 false
% 11.69/2.04  --dbg_dump_prop_clauses_file            -
% 11.69/2.04  --dbg_out_stat                          false
% 11.69/2.04  ------ Parsing...
% 11.69/2.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.69/2.04  
% 11.69/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.69/2.04  
% 11.69/2.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.69/2.04  
% 11.69/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.69/2.04  ------ Proving...
% 11.69/2.04  ------ Problem Properties 
% 11.69/2.04  
% 11.69/2.04  
% 11.69/2.04  clauses                                 34
% 11.69/2.04  conjectures                             5
% 11.69/2.04  EPR                                     7
% 11.69/2.04  Horn                                    25
% 11.69/2.04  unary                                   5
% 11.69/2.04  binary                                  17
% 11.69/2.04  lits                                    75
% 11.69/2.04  lits eq                                 14
% 11.69/2.04  fd_pure                                 0
% 11.69/2.04  fd_pseudo                               0
% 11.69/2.04  fd_cond                                 3
% 11.69/2.04  fd_pseudo_cond                          3
% 11.69/2.04  AC symbols                              0
% 11.69/2.04  
% 11.69/2.04  ------ Schedule dynamic 5 is on 
% 11.69/2.04  
% 11.69/2.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.69/2.04  
% 11.69/2.04  
% 11.69/2.04  ------ 
% 11.69/2.04  Current options:
% 11.69/2.04  ------ 
% 11.69/2.04  
% 11.69/2.04  ------ Input Options
% 11.69/2.04  
% 11.69/2.04  --out_options                           all
% 11.69/2.04  --tptp_safe_out                         true
% 11.69/2.04  --problem_path                          ""
% 11.69/2.04  --include_path                          ""
% 11.69/2.04  --clausifier                            res/vclausify_rel
% 11.69/2.04  --clausifier_options                    --mode clausify
% 11.69/2.04  --stdin                                 false
% 11.69/2.04  --stats_out                             all
% 11.69/2.04  
% 11.69/2.04  ------ General Options
% 11.69/2.04  
% 11.69/2.04  --fof                                   false
% 11.69/2.04  --time_out_real                         305.
% 11.69/2.04  --time_out_virtual                      -1.
% 11.69/2.04  --symbol_type_check                     false
% 11.69/2.04  --clausify_out                          false
% 11.69/2.04  --sig_cnt_out                           false
% 11.69/2.04  --trig_cnt_out                          false
% 11.69/2.04  --trig_cnt_out_tolerance                1.
% 11.69/2.04  --trig_cnt_out_sk_spl                   false
% 11.69/2.04  --abstr_cl_out                          false
% 11.69/2.04  
% 11.69/2.04  ------ Global Options
% 11.69/2.04  
% 11.69/2.04  --schedule                              default
% 11.69/2.04  --add_important_lit                     false
% 11.69/2.04  --prop_solver_per_cl                    1000
% 11.69/2.04  --min_unsat_core                        false
% 11.69/2.04  --soft_assumptions                      false
% 11.69/2.04  --soft_lemma_size                       3
% 11.69/2.04  --prop_impl_unit_size                   0
% 11.69/2.04  --prop_impl_unit                        []
% 11.69/2.04  --share_sel_clauses                     true
% 11.69/2.04  --reset_solvers                         false
% 11.69/2.04  --bc_imp_inh                            [conj_cone]
% 11.69/2.04  --conj_cone_tolerance                   3.
% 11.69/2.04  --extra_neg_conj                        none
% 11.69/2.04  --large_theory_mode                     true
% 11.69/2.04  --prolific_symb_bound                   200
% 11.69/2.04  --lt_threshold                          2000
% 11.69/2.04  --clause_weak_htbl                      true
% 11.69/2.04  --gc_record_bc_elim                     false
% 11.69/2.04  
% 11.69/2.04  ------ Preprocessing Options
% 11.69/2.04  
% 11.69/2.04  --preprocessing_flag                    true
% 11.69/2.04  --time_out_prep_mult                    0.1
% 11.69/2.04  --splitting_mode                        input
% 11.69/2.04  --splitting_grd                         true
% 11.69/2.04  --splitting_cvd                         false
% 11.69/2.04  --splitting_cvd_svl                     false
% 11.69/2.04  --splitting_nvd                         32
% 11.69/2.04  --sub_typing                            true
% 11.69/2.04  --prep_gs_sim                           true
% 11.69/2.04  --prep_unflatten                        true
% 11.69/2.04  --prep_res_sim                          true
% 11.69/2.04  --prep_upred                            true
% 11.69/2.04  --prep_sem_filter                       exhaustive
% 11.69/2.04  --prep_sem_filter_out                   false
% 11.69/2.04  --pred_elim                             true
% 11.69/2.04  --res_sim_input                         true
% 11.69/2.04  --eq_ax_congr_red                       true
% 11.69/2.04  --pure_diseq_elim                       true
% 11.69/2.04  --brand_transform                       false
% 11.69/2.04  --non_eq_to_eq                          false
% 11.69/2.04  --prep_def_merge                        true
% 11.69/2.04  --prep_def_merge_prop_impl              false
% 11.69/2.04  --prep_def_merge_mbd                    true
% 11.69/2.04  --prep_def_merge_tr_red                 false
% 11.69/2.04  --prep_def_merge_tr_cl                  false
% 11.69/2.04  --smt_preprocessing                     true
% 11.69/2.04  --smt_ac_axioms                         fast
% 11.69/2.04  --preprocessed_out                      false
% 11.69/2.04  --preprocessed_stats                    false
% 11.69/2.04  
% 11.69/2.04  ------ Abstraction refinement Options
% 11.69/2.04  
% 11.69/2.04  --abstr_ref                             []
% 11.69/2.04  --abstr_ref_prep                        false
% 11.69/2.04  --abstr_ref_until_sat                   false
% 11.69/2.04  --abstr_ref_sig_restrict                funpre
% 11.69/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 11.69/2.04  --abstr_ref_under                       []
% 11.69/2.04  
% 11.69/2.04  ------ SAT Options
% 11.69/2.04  
% 11.69/2.04  --sat_mode                              false
% 11.69/2.04  --sat_fm_restart_options                ""
% 11.69/2.04  --sat_gr_def                            false
% 11.69/2.04  --sat_epr_types                         true
% 11.69/2.04  --sat_non_cyclic_types                  false
% 11.69/2.04  --sat_finite_models                     false
% 11.69/2.04  --sat_fm_lemmas                         false
% 11.69/2.04  --sat_fm_prep                           false
% 11.69/2.04  --sat_fm_uc_incr                        true
% 11.69/2.04  --sat_out_model                         small
% 11.69/2.04  --sat_out_clauses                       false
% 11.69/2.04  
% 11.69/2.04  ------ QBF Options
% 11.69/2.04  
% 11.69/2.04  --qbf_mode                              false
% 11.69/2.04  --qbf_elim_univ                         false
% 11.69/2.04  --qbf_dom_inst                          none
% 11.69/2.04  --qbf_dom_pre_inst                      false
% 11.69/2.04  --qbf_sk_in                             false
% 11.69/2.04  --qbf_pred_elim                         true
% 11.69/2.04  --qbf_split                             512
% 11.69/2.04  
% 11.69/2.04  ------ BMC1 Options
% 11.69/2.04  
% 11.69/2.04  --bmc1_incremental                      false
% 11.69/2.04  --bmc1_axioms                           reachable_all
% 11.69/2.04  --bmc1_min_bound                        0
% 11.69/2.04  --bmc1_max_bound                        -1
% 11.69/2.04  --bmc1_max_bound_default                -1
% 11.69/2.04  --bmc1_symbol_reachability              true
% 11.69/2.04  --bmc1_property_lemmas                  false
% 11.69/2.04  --bmc1_k_induction                      false
% 11.69/2.04  --bmc1_non_equiv_states                 false
% 11.69/2.04  --bmc1_deadlock                         false
% 11.69/2.04  --bmc1_ucm                              false
% 11.69/2.04  --bmc1_add_unsat_core                   none
% 11.69/2.04  --bmc1_unsat_core_children              false
% 11.69/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 11.69/2.04  --bmc1_out_stat                         full
% 11.69/2.04  --bmc1_ground_init                      false
% 11.69/2.04  --bmc1_pre_inst_next_state              false
% 11.69/2.04  --bmc1_pre_inst_state                   false
% 11.69/2.04  --bmc1_pre_inst_reach_state             false
% 11.69/2.04  --bmc1_out_unsat_core                   false
% 11.69/2.04  --bmc1_aig_witness_out                  false
% 11.69/2.04  --bmc1_verbose                          false
% 11.69/2.04  --bmc1_dump_clauses_tptp                false
% 11.69/2.04  --bmc1_dump_unsat_core_tptp             false
% 11.69/2.04  --bmc1_dump_file                        -
% 11.69/2.04  --bmc1_ucm_expand_uc_limit              128
% 11.69/2.04  --bmc1_ucm_n_expand_iterations          6
% 11.69/2.04  --bmc1_ucm_extend_mode                  1
% 11.69/2.04  --bmc1_ucm_init_mode                    2
% 11.69/2.04  --bmc1_ucm_cone_mode                    none
% 11.69/2.04  --bmc1_ucm_reduced_relation_type        0
% 11.69/2.04  --bmc1_ucm_relax_model                  4
% 11.69/2.04  --bmc1_ucm_full_tr_after_sat            true
% 11.69/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 11.69/2.04  --bmc1_ucm_layered_model                none
% 11.69/2.04  --bmc1_ucm_max_lemma_size               10
% 11.69/2.04  
% 11.69/2.04  ------ AIG Options
% 11.69/2.04  
% 11.69/2.04  --aig_mode                              false
% 11.69/2.04  
% 11.69/2.04  ------ Instantiation Options
% 11.69/2.04  
% 11.69/2.04  --instantiation_flag                    true
% 11.69/2.04  --inst_sos_flag                         false
% 11.69/2.04  --inst_sos_phase                        true
% 11.69/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.69/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.69/2.04  --inst_lit_sel_side                     none
% 11.69/2.04  --inst_solver_per_active                1400
% 11.69/2.04  --inst_solver_calls_frac                1.
% 11.69/2.04  --inst_passive_queue_type               priority_queues
% 11.69/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.69/2.04  --inst_passive_queues_freq              [25;2]
% 11.69/2.04  --inst_dismatching                      true
% 11.69/2.04  --inst_eager_unprocessed_to_passive     true
% 11.69/2.04  --inst_prop_sim_given                   true
% 11.69/2.04  --inst_prop_sim_new                     false
% 11.69/2.04  --inst_subs_new                         false
% 11.69/2.04  --inst_eq_res_simp                      false
% 11.69/2.04  --inst_subs_given                       false
% 11.69/2.04  --inst_orphan_elimination               true
% 11.69/2.04  --inst_learning_loop_flag               true
% 11.69/2.04  --inst_learning_start                   3000
% 11.69/2.04  --inst_learning_factor                  2
% 11.69/2.04  --inst_start_prop_sim_after_learn       3
% 11.69/2.04  --inst_sel_renew                        solver
% 11.69/2.04  --inst_lit_activity_flag                true
% 11.69/2.04  --inst_restr_to_given                   false
% 11.69/2.04  --inst_activity_threshold               500
% 11.69/2.04  --inst_out_proof                        true
% 11.69/2.04  
% 11.69/2.04  ------ Resolution Options
% 11.69/2.04  
% 11.69/2.04  --resolution_flag                       false
% 11.69/2.04  --res_lit_sel                           adaptive
% 11.69/2.04  --res_lit_sel_side                      none
% 11.69/2.04  --res_ordering                          kbo
% 11.69/2.04  --res_to_prop_solver                    active
% 11.69/2.04  --res_prop_simpl_new                    false
% 11.69/2.04  --res_prop_simpl_given                  true
% 11.69/2.04  --res_passive_queue_type                priority_queues
% 11.69/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.69/2.04  --res_passive_queues_freq               [15;5]
% 11.69/2.04  --res_forward_subs                      full
% 11.69/2.04  --res_backward_subs                     full
% 11.69/2.04  --res_forward_subs_resolution           true
% 11.69/2.04  --res_backward_subs_resolution          true
% 11.69/2.04  --res_orphan_elimination                true
% 11.69/2.04  --res_time_limit                        2.
% 11.69/2.04  --res_out_proof                         true
% 11.69/2.04  
% 11.69/2.04  ------ Superposition Options
% 11.69/2.04  
% 11.69/2.04  --superposition_flag                    true
% 11.69/2.04  --sup_passive_queue_type                priority_queues
% 11.69/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.69/2.04  --sup_passive_queues_freq               [8;1;4]
% 11.69/2.04  --demod_completeness_check              fast
% 11.69/2.04  --demod_use_ground                      true
% 11.69/2.04  --sup_to_prop_solver                    passive
% 11.69/2.04  --sup_prop_simpl_new                    true
% 11.69/2.04  --sup_prop_simpl_given                  true
% 11.69/2.04  --sup_fun_splitting                     false
% 11.69/2.04  --sup_smt_interval                      50000
% 11.69/2.04  
% 11.69/2.04  ------ Superposition Simplification Setup
% 11.69/2.04  
% 11.69/2.04  --sup_indices_passive                   []
% 11.69/2.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.69/2.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.69/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.69/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 11.69/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.69/2.04  --sup_full_bw                           [BwDemod]
% 11.69/2.04  --sup_immed_triv                        [TrivRules]
% 11.69/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.69/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.69/2.04  --sup_immed_bw_main                     []
% 11.69/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.69/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 11.69/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.69/2.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.69/2.04  
% 11.69/2.04  ------ Combination Options
% 11.69/2.04  
% 11.69/2.04  --comb_res_mult                         3
% 11.69/2.04  --comb_sup_mult                         2
% 11.69/2.04  --comb_inst_mult                        10
% 11.69/2.04  
% 11.69/2.04  ------ Debug Options
% 11.69/2.04  
% 11.69/2.04  --dbg_backtrace                         false
% 11.69/2.04  --dbg_dump_prop_clauses                 false
% 11.69/2.04  --dbg_dump_prop_clauses_file            -
% 11.69/2.04  --dbg_out_stat                          false
% 11.69/2.04  
% 11.69/2.04  
% 11.69/2.04  
% 11.69/2.04  
% 11.69/2.04  ------ Proving...
% 11.69/2.04  
% 11.69/2.04  
% 11.69/2.04  % SZS status Theorem for theBenchmark.p
% 11.69/2.04  
% 11.69/2.04  % SZS output start CNFRefutation for theBenchmark.p
% 11.69/2.04  
% 11.69/2.04  fof(f2,axiom,(
% 11.69/2.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f17,plain,(
% 11.69/2.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.69/2.04    inference(ennf_transformation,[],[f2])).
% 11.69/2.04  
% 11.69/2.04  fof(f33,plain,(
% 11.69/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.69/2.04    inference(nnf_transformation,[],[f17])).
% 11.69/2.04  
% 11.69/2.04  fof(f34,plain,(
% 11.69/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.69/2.04    inference(rectify,[],[f33])).
% 11.69/2.04  
% 11.69/2.04  fof(f35,plain,(
% 11.69/2.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.69/2.04    introduced(choice_axiom,[])).
% 11.69/2.04  
% 11.69/2.04  fof(f36,plain,(
% 11.69/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.69/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 11.69/2.04  
% 11.69/2.04  fof(f57,plain,(
% 11.69/2.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 11.69/2.04    inference(cnf_transformation,[],[f36])).
% 11.69/2.04  
% 11.69/2.04  fof(f3,axiom,(
% 11.69/2.04    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f37,plain,(
% 11.69/2.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.69/2.04    inference(nnf_transformation,[],[f3])).
% 11.69/2.04  
% 11.69/2.04  fof(f38,plain,(
% 11.69/2.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.69/2.04    inference(rectify,[],[f37])).
% 11.69/2.04  
% 11.69/2.04  fof(f39,plain,(
% 11.69/2.04    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 11.69/2.04    introduced(choice_axiom,[])).
% 11.69/2.04  
% 11.69/2.04  fof(f40,plain,(
% 11.69/2.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.69/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 11.69/2.04  
% 11.69/2.04  fof(f59,plain,(
% 11.69/2.04    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.69/2.04    inference(cnf_transformation,[],[f40])).
% 11.69/2.04  
% 11.69/2.04  fof(f90,plain,(
% 11.69/2.04    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 11.69/2.04    inference(equality_resolution,[],[f59])).
% 11.69/2.04  
% 11.69/2.04  fof(f5,axiom,(
% 11.69/2.04    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f42,plain,(
% 11.69/2.04    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.69/2.04    inference(nnf_transformation,[],[f5])).
% 11.69/2.04  
% 11.69/2.04  fof(f65,plain,(
% 11.69/2.04    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 11.69/2.04    inference(cnf_transformation,[],[f42])).
% 11.69/2.04  
% 11.69/2.04  fof(f15,conjecture,(
% 11.69/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f16,negated_conjecture,(
% 11.69/2.04    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 11.69/2.04    inference(negated_conjecture,[],[f15])).
% 11.69/2.04  
% 11.69/2.04  fof(f27,plain,(
% 11.69/2.04    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.69/2.04    inference(ennf_transformation,[],[f16])).
% 11.69/2.04  
% 11.69/2.04  fof(f28,plain,(
% 11.69/2.04    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.69/2.04    inference(flattening,[],[f27])).
% 11.69/2.04  
% 11.69/2.04  fof(f48,plain,(
% 11.69/2.04    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.69/2.04    inference(nnf_transformation,[],[f28])).
% 11.69/2.04  
% 11.69/2.04  fof(f49,plain,(
% 11.69/2.04    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.69/2.04    inference(flattening,[],[f48])).
% 11.69/2.04  
% 11.69/2.04  fof(f50,plain,(
% 11.69/2.04    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.69/2.04    inference(rectify,[],[f49])).
% 11.69/2.04  
% 11.69/2.04  fof(f52,plain,(
% 11.69/2.04    ( ! [X2,X1] : (? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) => (~r2_hidden(X1,sK7) & r2_hidden(sK7,X2))) )),
% 11.69/2.04    introduced(choice_axiom,[])).
% 11.69/2.04  
% 11.69/2.04  fof(f51,plain,(
% 11.69/2.04    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK5,X3) & r2_hidden(X3,sK6)) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & (! [X4] : (r2_hidden(sK5,X4) | ~r2_hidden(X4,sK6)) | r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & r2_hidden(sK5,sK4) & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))))),
% 11.69/2.04    introduced(choice_axiom,[])).
% 11.69/2.04  
% 11.69/2.04  fof(f53,plain,(
% 11.69/2.04    ((~r2_hidden(sK5,sK7) & r2_hidden(sK7,sK6)) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & (! [X4] : (r2_hidden(sK5,X4) | ~r2_hidden(X4,sK6)) | r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & r2_hidden(sK5,sK4) & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4)))),
% 11.69/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f50,f52,f51])).
% 11.69/2.04  
% 11.69/2.04  fof(f83,plain,(
% 11.69/2.04    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4)))),
% 11.69/2.04    inference(cnf_transformation,[],[f53])).
% 11.69/2.04  
% 11.69/2.04  fof(f9,axiom,(
% 11.69/2.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f19,plain,(
% 11.69/2.04    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.69/2.04    inference(ennf_transformation,[],[f9])).
% 11.69/2.04  
% 11.69/2.04  fof(f75,plain,(
% 11.69/2.04    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.69/2.04    inference(cnf_transformation,[],[f19])).
% 11.69/2.04  
% 11.69/2.04  fof(f11,axiom,(
% 11.69/2.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f21,plain,(
% 11.69/2.04    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.69/2.04    inference(ennf_transformation,[],[f11])).
% 11.69/2.04  
% 11.69/2.04  fof(f78,plain,(
% 11.69/2.04    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.69/2.04    inference(cnf_transformation,[],[f21])).
% 11.69/2.04  
% 11.69/2.04  fof(f86,plain,(
% 11.69/2.04    r2_hidden(sK7,sK6) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))),
% 11.69/2.04    inference(cnf_transformation,[],[f53])).
% 11.69/2.04  
% 11.69/2.04  fof(f85,plain,(
% 11.69/2.04    ( ! [X4] : (r2_hidden(sK5,X4) | ~r2_hidden(X4,sK6) | r2_hidden(sK5,k8_setfam_1(sK4,sK6))) )),
% 11.69/2.04    inference(cnf_transformation,[],[f53])).
% 11.69/2.04  
% 11.69/2.04  fof(f4,axiom,(
% 11.69/2.04    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f41,plain,(
% 11.69/2.04    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 11.69/2.04    inference(nnf_transformation,[],[f4])).
% 11.69/2.04  
% 11.69/2.04  fof(f63,plain,(
% 11.69/2.04    ( ! [X0,X1] : (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 11.69/2.04    inference(cnf_transformation,[],[f41])).
% 11.69/2.04  
% 11.69/2.04  fof(f64,plain,(
% 11.69/2.04    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) )),
% 11.69/2.04    inference(cnf_transformation,[],[f41])).
% 11.69/2.04  
% 11.69/2.04  fof(f87,plain,(
% 11.69/2.04    ~r2_hidden(sK5,sK7) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))),
% 11.69/2.04    inference(cnf_transformation,[],[f53])).
% 11.69/2.04  
% 11.69/2.04  fof(f14,axiom,(
% 11.69/2.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f25,plain,(
% 11.69/2.04    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 11.69/2.04    inference(ennf_transformation,[],[f14])).
% 11.69/2.04  
% 11.69/2.04  fof(f26,plain,(
% 11.69/2.04    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 11.69/2.04    inference(flattening,[],[f25])).
% 11.69/2.04  
% 11.69/2.04  fof(f46,plain,(
% 11.69/2.04    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 11.69/2.04    introduced(choice_axiom,[])).
% 11.69/2.04  
% 11.69/2.04  fof(f47,plain,(
% 11.69/2.04    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 11.69/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f46])).
% 11.69/2.04  
% 11.69/2.04  fof(f81,plain,(
% 11.69/2.04    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 11.69/2.04    inference(cnf_transformation,[],[f47])).
% 11.69/2.04  
% 11.69/2.04  fof(f66,plain,(
% 11.69/2.04    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.69/2.04    inference(cnf_transformation,[],[f42])).
% 11.69/2.04  
% 11.69/2.04  fof(f82,plain,(
% 11.69/2.04    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK3(X0,X1))) )),
% 11.69/2.04    inference(cnf_transformation,[],[f47])).
% 11.69/2.04  
% 11.69/2.04  fof(f12,axiom,(
% 11.69/2.04    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f22,plain,(
% 11.69/2.04    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 11.69/2.04    inference(ennf_transformation,[],[f12])).
% 11.69/2.04  
% 11.69/2.04  fof(f79,plain,(
% 11.69/2.04    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 11.69/2.04    inference(cnf_transformation,[],[f22])).
% 11.69/2.04  
% 11.69/2.04  fof(f56,plain,(
% 11.69/2.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.69/2.04    inference(cnf_transformation,[],[f36])).
% 11.69/2.04  
% 11.69/2.04  fof(f6,axiom,(
% 11.69/2.04    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f43,plain,(
% 11.69/2.04    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 11.69/2.04    inference(nnf_transformation,[],[f6])).
% 11.69/2.04  
% 11.69/2.04  fof(f44,plain,(
% 11.69/2.04    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 11.69/2.04    inference(flattening,[],[f43])).
% 11.69/2.04  
% 11.69/2.04  fof(f67,plain,(
% 11.69/2.04    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 11.69/2.04    inference(cnf_transformation,[],[f44])).
% 11.69/2.04  
% 11.69/2.04  fof(f76,plain,(
% 11.69/2.04    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.69/2.04    inference(cnf_transformation,[],[f19])).
% 11.69/2.04  
% 11.69/2.04  fof(f92,plain,(
% 11.69/2.04    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.69/2.04    inference(equality_resolution,[],[f76])).
% 11.69/2.04  
% 11.69/2.04  fof(f8,axiom,(
% 11.69/2.04    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f74,plain,(
% 11.69/2.04    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.69/2.04    inference(cnf_transformation,[],[f8])).
% 11.69/2.04  
% 11.69/2.04  fof(f1,axiom,(
% 11.69/2.04    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.69/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.04  
% 11.69/2.04  fof(f29,plain,(
% 11.69/2.04    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.69/2.04    inference(nnf_transformation,[],[f1])).
% 11.69/2.04  
% 11.69/2.04  fof(f30,plain,(
% 11.69/2.04    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.69/2.04    inference(rectify,[],[f29])).
% 11.69/2.04  
% 11.69/2.04  fof(f31,plain,(
% 11.69/2.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.69/2.04    introduced(choice_axiom,[])).
% 11.69/2.04  
% 11.69/2.04  fof(f32,plain,(
% 11.69/2.04    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.69/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 11.69/2.04  
% 11.69/2.04  fof(f54,plain,(
% 11.69/2.04    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.69/2.04    inference(cnf_transformation,[],[f32])).
% 11.69/2.04  
% 11.69/2.04  fof(f55,plain,(
% 11.69/2.04    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 11.69/2.04    inference(cnf_transformation,[],[f32])).
% 11.69/2.04  
% 11.69/2.04  fof(f60,plain,(
% 11.69/2.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.69/2.04    inference(cnf_transformation,[],[f40])).
% 11.69/2.04  
% 11.69/2.04  fof(f88,plain,(
% 11.69/2.04    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 11.69/2.04    inference(equality_resolution,[],[f60])).
% 11.69/2.04  
% 11.69/2.04  fof(f89,plain,(
% 11.69/2.04    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 11.69/2.04    inference(equality_resolution,[],[f88])).
% 11.69/2.04  
% 11.69/2.04  fof(f68,plain,(
% 11.69/2.04    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 11.69/2.04    inference(cnf_transformation,[],[f44])).
% 11.69/2.04  
% 11.69/2.04  fof(f91,plain,(
% 11.69/2.04    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 11.69/2.04    inference(equality_resolution,[],[f68])).
% 11.69/2.04  
% 11.69/2.04  fof(f84,plain,(
% 11.69/2.04    r2_hidden(sK5,sK4)),
% 11.69/2.04    inference(cnf_transformation,[],[f53])).
% 11.69/2.04  
% 11.69/2.04  cnf(c_3,plain,
% 11.69/2.04      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 11.69/2.04      inference(cnf_transformation,[],[f57]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_1216,plain,
% 11.69/2.04      ( r1_tarski(X0,X1) = iProver_top
% 11.69/2.04      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 11.69/2.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_8,plain,
% 11.69/2.04      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 11.69/2.04      inference(cnf_transformation,[],[f90]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_1211,plain,
% 11.69/2.04      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 11.69/2.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_3111,plain,
% 11.69/2.04      ( sK1(k1_tarski(X0),X1) = X0
% 11.69/2.04      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 11.69/2.04      inference(superposition,[status(thm)],[c_1216,c_1211]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_12,plain,
% 11.69/2.04      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 11.69/2.04      inference(cnf_transformation,[],[f65]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_1207,plain,
% 11.69/2.04      ( r1_tarski(k1_tarski(X0),X1) != iProver_top
% 11.69/2.04      | r2_hidden(X0,X1) = iProver_top ),
% 11.69/2.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_12497,plain,
% 11.69/2.04      ( sK1(k1_tarski(X0),X1) = X0 | r2_hidden(X0,X1) = iProver_top ),
% 11.69/2.04      inference(superposition,[status(thm)],[c_3111,c_1207]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_33,negated_conjecture,
% 11.69/2.04      ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
% 11.69/2.04      inference(cnf_transformation,[],[f83]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_1187,plain,
% 11.69/2.04      ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) = iProver_top ),
% 11.69/2.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_22,plain,
% 11.69/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.69/2.04      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 11.69/2.04      | k1_xboole_0 = X0 ),
% 11.69/2.04      inference(cnf_transformation,[],[f75]) ).
% 11.69/2.04  
% 11.69/2.04  cnf(c_1198,plain,
% 11.69/2.04      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 11.69/2.05      | k1_xboole_0 = X1
% 11.69/2.05      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_5175,plain,
% 11.69/2.05      ( k6_setfam_1(sK4,sK6) = k8_setfam_1(sK4,sK6) | sK6 = k1_xboole_0 ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_1187,c_1198]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_24,plain,
% 11.69/2.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.69/2.05      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 11.69/2.05      inference(cnf_transformation,[],[f78]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1196,plain,
% 11.69/2.05      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 11.69/2.05      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_3235,plain,
% 11.69/2.05      ( k6_setfam_1(sK4,sK6) = k1_setfam_1(sK6) ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_1187,c_1196]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_5178,plain,
% 11.69/2.05      ( k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6) | sK6 = k1_xboole_0 ),
% 11.69/2.05      inference(light_normalisation,[status(thm)],[c_5175,c_3235]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_30,negated_conjecture,
% 11.69/2.05      ( r2_hidden(sK7,sK6) | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
% 11.69/2.05      inference(cnf_transformation,[],[f86]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1190,plain,
% 11.69/2.05      ( r2_hidden(sK7,sK6) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_6141,plain,
% 11.69/2.05      ( sK6 = k1_xboole_0
% 11.69/2.05      | r2_hidden(sK7,sK6) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_5178,c_1190]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_12622,plain,
% 11.69/2.05      ( sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
% 11.69/2.05      | sK6 = k1_xboole_0
% 11.69/2.05      | r2_hidden(sK7,sK6) = iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_12497,c_6141]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_31,negated_conjecture,
% 11.69/2.05      ( ~ r2_hidden(X0,sK6)
% 11.69/2.05      | r2_hidden(sK5,X0)
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
% 11.69/2.05      inference(cnf_transformation,[],[f85]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1189,plain,
% 11.69/2.05      ( r2_hidden(X0,sK6) != iProver_top
% 11.69/2.05      | r2_hidden(sK5,X0) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_16287,plain,
% 11.69/2.05      ( sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
% 11.69/2.05      | sK6 = k1_xboole_0
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,sK7) = iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_12622,c_1189]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_10,plain,
% 11.69/2.05      ( r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 11.69/2.05      inference(cnf_transformation,[],[f63]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1652,plain,
% 11.69/2.05      ( r2_hidden(sK5,k8_setfam_1(sK4,sK6))
% 11.69/2.05      | k4_xboole_0(k1_tarski(sK5),k8_setfam_1(sK4,sK6)) != k1_xboole_0 ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_10]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1653,plain,
% 11.69/2.05      ( k4_xboole_0(k1_tarski(sK5),k8_setfam_1(sK4,sK6)) != k1_xboole_0
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_1652]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_9,plain,
% 11.69/2.05      ( ~ r2_hidden(X0,X1)
% 11.69/2.05      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
% 11.69/2.05      inference(cnf_transformation,[],[f64]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_3007,plain,
% 11.69/2.05      ( ~ r2_hidden(sK5,X0)
% 11.69/2.05      | k4_xboole_0(k1_tarski(sK5),X0) = k1_xboole_0 ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_9]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_4775,plain,
% 11.69/2.05      ( ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6))
% 11.69/2.05      | k4_xboole_0(k1_tarski(sK5),k8_setfam_1(sK4,sK6)) = k1_xboole_0 ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_3007]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_29,negated_conjecture,
% 11.69/2.05      ( ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) | ~ r2_hidden(sK5,sK7) ),
% 11.69/2.05      inference(cnf_transformation,[],[f87]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1191,plain,
% 11.69/2.05      ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top
% 11.69/2.05      | r2_hidden(sK5,sK7) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_6140,plain,
% 11.69/2.05      ( sK6 = k1_xboole_0
% 11.69/2.05      | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top
% 11.69/2.05      | r2_hidden(sK5,sK7) != iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_5178,c_1191]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_12623,plain,
% 11.69/2.05      ( sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
% 11.69/2.05      | sK6 = k1_xboole_0
% 11.69/2.05      | r2_hidden(sK5,sK7) != iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_12497,c_6140]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_12757,plain,
% 11.69/2.05      ( ~ r2_hidden(sK5,sK7)
% 11.69/2.05      | sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
% 11.69/2.05      | sK6 = k1_xboole_0 ),
% 11.69/2.05      inference(predicate_to_equality_rev,[status(thm)],[c_12623]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_16328,plain,
% 11.69/2.05      ( r2_hidden(sK5,k8_setfam_1(sK4,sK6))
% 11.69/2.05      | r2_hidden(sK5,sK7)
% 11.69/2.05      | sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
% 11.69/2.05      | sK6 = k1_xboole_0 ),
% 11.69/2.05      inference(predicate_to_equality_rev,[status(thm)],[c_16287]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_16472,plain,
% 11.69/2.05      ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
% 11.69/2.05      | sK6 = k1_xboole_0
% 11.69/2.05      | sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5 ),
% 11.69/2.05      inference(global_propositional_subsumption,
% 11.69/2.05                [status(thm)],
% 11.69/2.05                [c_16287,c_1653,c_4775,c_12757,c_16328]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_16473,plain,
% 11.69/2.05      ( sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
% 11.69/2.05      | sK6 = k1_xboole_0
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 11.69/2.05      inference(renaming,[status(thm)],[c_16472]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1210,plain,
% 11.69/2.05      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
% 11.69/2.05      | r2_hidden(X0,X1) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_16481,plain,
% 11.69/2.05      ( k4_xboole_0(k1_tarski(sK5),k8_setfam_1(sK4,sK6)) = k1_xboole_0
% 11.69/2.05      | sK1(k1_tarski(sK5),k1_setfam_1(sK6)) = sK5
% 11.69/2.05      | sK6 = k1_xboole_0 ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_16473,c_1210]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1720,plain,
% 11.69/2.05      ( ~ r2_hidden(sK7,sK6)
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6))
% 11.69/2.05      | r2_hidden(sK5,sK7) ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_31]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_6216,plain,
% 11.69/2.05      ( ~ r2_hidden(sK5,k1_setfam_1(sK6))
% 11.69/2.05      | ~ r2_hidden(sK5,sK7)
% 11.69/2.05      | sK6 = k1_xboole_0 ),
% 11.69/2.05      inference(predicate_to_equality_rev,[status(thm)],[c_6140]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_6217,plain,
% 11.69/2.05      ( r2_hidden(sK7,sK6)
% 11.69/2.05      | ~ r2_hidden(sK5,k1_setfam_1(sK6))
% 11.69/2.05      | sK6 = k1_xboole_0 ),
% 11.69/2.05      inference(predicate_to_equality_rev,[status(thm)],[c_6141]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_28,plain,
% 11.69/2.05      ( r1_tarski(X0,k1_setfam_1(X1))
% 11.69/2.05      | r2_hidden(sK3(X1,X0),X1)
% 11.69/2.05      | k1_xboole_0 = X1 ),
% 11.69/2.05      inference(cnf_transformation,[],[f81]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1192,plain,
% 11.69/2.05      ( k1_xboole_0 = X0
% 11.69/2.05      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
% 11.69/2.05      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_2251,plain,
% 11.69/2.05      ( sK6 = k1_xboole_0
% 11.69/2.05      | r1_tarski(X0,k1_setfam_1(sK6)) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,sK3(sK6,X0)) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_1192,c_1189]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_11,plain,
% 11.69/2.05      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 11.69/2.05      inference(cnf_transformation,[],[f66]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1208,plain,
% 11.69/2.05      ( r1_tarski(k1_tarski(X0),X1) = iProver_top
% 11.69/2.05      | r2_hidden(X0,X1) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_27,plain,
% 11.69/2.05      ( ~ r1_tarski(X0,sK3(X1,X0))
% 11.69/2.05      | r1_tarski(X0,k1_setfam_1(X1))
% 11.69/2.05      | k1_xboole_0 = X1 ),
% 11.69/2.05      inference(cnf_transformation,[],[f82]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1193,plain,
% 11.69/2.05      ( k1_xboole_0 = X0
% 11.69/2.05      | r1_tarski(X1,sK3(X0,X1)) != iProver_top
% 11.69/2.05      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_5412,plain,
% 11.69/2.05      ( k1_xboole_0 = X0
% 11.69/2.05      | r1_tarski(k1_tarski(X1),k1_setfam_1(X0)) = iProver_top
% 11.69/2.05      | r2_hidden(X1,sK3(X0,k1_tarski(X1))) != iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_1208,c_1193]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_50916,plain,
% 11.69/2.05      ( sK6 = k1_xboole_0
% 11.69/2.05      | r1_tarski(k1_tarski(sK5),k1_setfam_1(sK6)) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_2251,c_5412]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_51779,plain,
% 11.69/2.05      ( sK6 = k1_xboole_0
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,k1_setfam_1(sK6)) = iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_50916,c_1207]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_51797,plain,
% 11.69/2.05      ( r2_hidden(sK5,k8_setfam_1(sK4,sK6))
% 11.69/2.05      | r2_hidden(sK5,k1_setfam_1(sK6))
% 11.69/2.05      | sK6 = k1_xboole_0 ),
% 11.69/2.05      inference(predicate_to_equality_rev,[status(thm)],[c_51779]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_51803,plain,
% 11.69/2.05      ( k4_xboole_0(k1_tarski(sK5),k8_setfam_1(sK4,sK6)) = k1_xboole_0
% 11.69/2.05      | sK6 = k1_xboole_0 ),
% 11.69/2.05      inference(global_propositional_subsumption,
% 11.69/2.05                [status(thm)],
% 11.69/2.05                [c_16481,c_1720,c_4775,c_6216,c_6217,c_51797]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1209,plain,
% 11.69/2.05      ( k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0
% 11.69/2.05      | r2_hidden(X0,X1) = iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_51808,plain,
% 11.69/2.05      ( sK6 = k1_xboole_0
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_51803,c_1209]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_52320,plain,
% 11.69/2.05      ( sK6 = k1_xboole_0 | r2_hidden(sK5,sK7) != iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_51808,c_1191]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_25,plain,
% 11.69/2.05      ( r1_tarski(k1_setfam_1(X0),X1) | ~ r2_hidden(X1,X0) ),
% 11.69/2.05      inference(cnf_transformation,[],[f79]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_4012,plain,
% 11.69/2.05      ( r1_tarski(k1_setfam_1(X0),sK7) | ~ r2_hidden(sK7,X0) ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_25]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_15221,plain,
% 11.69/2.05      ( r1_tarski(k1_setfam_1(sK6),sK7) | ~ r2_hidden(sK7,sK6) ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_4012]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_15222,plain,
% 11.69/2.05      ( r1_tarski(k1_setfam_1(sK6),sK7) = iProver_top
% 11.69/2.05      | r2_hidden(sK7,sK6) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_15221]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_4,plain,
% 11.69/2.05      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 11.69/2.05      inference(cnf_transformation,[],[f56]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_2006,plain,
% 11.69/2.05      ( ~ r1_tarski(X0,sK7) | ~ r2_hidden(sK5,X0) | r2_hidden(sK5,sK7) ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_4]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_4011,plain,
% 11.69/2.05      ( ~ r1_tarski(k1_setfam_1(X0),sK7)
% 11.69/2.05      | ~ r2_hidden(sK5,k1_setfam_1(X0))
% 11.69/2.05      | r2_hidden(sK5,sK7) ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_2006]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_42762,plain,
% 11.69/2.05      ( ~ r1_tarski(k1_setfam_1(sK6),sK7)
% 11.69/2.05      | ~ r2_hidden(sK5,k1_setfam_1(sK6))
% 11.69/2.05      | r2_hidden(sK5,sK7) ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_4011]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_42763,plain,
% 11.69/2.05      ( r1_tarski(k1_setfam_1(sK6),sK7) != iProver_top
% 11.69/2.05      | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top
% 11.69/2.05      | r2_hidden(sK5,sK7) = iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_42762]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_15,plain,
% 11.69/2.05      ( r2_hidden(X0,X1)
% 11.69/2.05      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ),
% 11.69/2.05      inference(cnf_transformation,[],[f67]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1204,plain,
% 11.69/2.05      ( r2_hidden(X0,X1) = iProver_top
% 11.69/2.05      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_12609,plain,
% 11.69/2.05      ( sK1(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X2))) = X0
% 11.69/2.05      | r2_hidden(X0,X1) = iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_12497,c_1204]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_16779,plain,
% 11.69/2.05      ( sK1(k1_tarski(sK5),k4_xboole_0(k1_setfam_1(sK6),k1_tarski(X0))) = sK5
% 11.69/2.05      | sK6 = k1_xboole_0
% 11.69/2.05      | r2_hidden(sK7,sK6) = iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_12609,c_6141]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_39,plain,
% 11.69/2.05      ( r2_hidden(sK7,sK6) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_51991,plain,
% 11.69/2.05      ( sK6 = k1_xboole_0 | r2_hidden(sK7,sK6) = iProver_top ),
% 11.69/2.05      inference(global_propositional_subsumption,
% 11.69/2.05                [status(thm)],
% 11.69/2.05                [c_16779,c_39,c_51808]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_52315,plain,
% 11.69/2.05      ( sK6 = k1_xboole_0
% 11.69/2.05      | r2_hidden(sK5,k1_setfam_1(sK6)) = iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_5178,c_51808]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_52750,plain,
% 11.69/2.05      ( sK6 = k1_xboole_0 ),
% 11.69/2.05      inference(global_propositional_subsumption,
% 11.69/2.05                [status(thm)],
% 11.69/2.05                [c_52320,c_15222,c_42763,c_51991,c_52315]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_52986,plain,
% 11.69/2.05      ( r2_hidden(sK7,k1_xboole_0) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,k8_setfam_1(sK4,k1_xboole_0)) != iProver_top ),
% 11.69/2.05      inference(demodulation,[status(thm)],[c_52750,c_1190]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_21,plain,
% 11.69/2.05      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 11.69/2.05      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 11.69/2.05      inference(cnf_transformation,[],[f92]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1199,plain,
% 11.69/2.05      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 11.69/2.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_20,plain,
% 11.69/2.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.69/2.05      inference(cnf_transformation,[],[f74]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1200,plain,
% 11.69/2.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1276,plain,
% 11.69/2.05      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 11.69/2.05      inference(forward_subsumption_resolution,
% 11.69/2.05                [status(thm)],
% 11.69/2.05                [c_1199,c_1200]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_52991,plain,
% 11.69/2.05      ( r2_hidden(sK7,k1_xboole_0) = iProver_top
% 11.69/2.05      | r2_hidden(sK5,sK4) != iProver_top ),
% 11.69/2.05      inference(demodulation,[status(thm)],[c_52986,c_1276]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1,plain,
% 11.69/2.05      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.69/2.05      inference(cnf_transformation,[],[f54]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_48398,plain,
% 11.69/2.05      ( ~ r2_hidden(sK7,X0) | ~ v1_xboole_0(X0) ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_1]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_48404,plain,
% 11.69/2.05      ( r2_hidden(sK7,X0) != iProver_top
% 11.69/2.05      | v1_xboole_0(X0) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_48398]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_48406,plain,
% 11.69/2.05      ( r2_hidden(sK7,k1_xboole_0) != iProver_top
% 11.69/2.05      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.69/2.05      inference(instantiation,[status(thm)],[c_48404]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_0,plain,
% 11.69/2.05      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 11.69/2.05      inference(cnf_transformation,[],[f55]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1219,plain,
% 11.69/2.05      ( r2_hidden(sK0(X0),X0) = iProver_top
% 11.69/2.05      | v1_xboole_0(X0) = iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_7,plain,
% 11.69/2.05      ( r2_hidden(X0,k1_tarski(X0)) ),
% 11.69/2.05      inference(cnf_transformation,[],[f89]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1212,plain,
% 11.69/2.05      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_2929,plain,
% 11.69/2.05      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_xboole_0 ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_1212,c_1210]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_14,plain,
% 11.69/2.05      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) ),
% 11.69/2.05      inference(cnf_transformation,[],[f91]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_1205,plain,
% 11.69/2.05      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) != iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_7796,plain,
% 11.69/2.05      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_2929,c_1205]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_7843,plain,
% 11.69/2.05      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 11.69/2.05      inference(superposition,[status(thm)],[c_1219,c_7796]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_32,negated_conjecture,
% 11.69/2.05      ( r2_hidden(sK5,sK4) ),
% 11.69/2.05      inference(cnf_transformation,[],[f84]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(c_35,plain,
% 11.69/2.05      ( r2_hidden(sK5,sK4) = iProver_top ),
% 11.69/2.05      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.69/2.05  
% 11.69/2.05  cnf(contradiction,plain,
% 11.69/2.05      ( $false ),
% 11.69/2.05      inference(minisat,[status(thm)],[c_52991,c_48406,c_7843,c_35]) ).
% 11.69/2.05  
% 11.69/2.05  
% 11.69/2.05  % SZS output end CNFRefutation for theBenchmark.p
% 11.69/2.05  
% 11.69/2.05  ------                               Statistics
% 11.69/2.05  
% 11.69/2.05  ------ General
% 11.69/2.05  
% 11.69/2.05  abstr_ref_over_cycles:                  0
% 11.69/2.05  abstr_ref_under_cycles:                 0
% 11.69/2.05  gc_basic_clause_elim:                   0
% 11.69/2.05  forced_gc_time:                         0
% 11.69/2.05  parsing_time:                           0.013
% 11.69/2.05  unif_index_cands_time:                  0.
% 11.69/2.05  unif_index_add_time:                    0.
% 11.69/2.05  orderings_time:                         0.
% 11.69/2.05  out_proof_time:                         0.015
% 11.69/2.05  total_time:                             1.167
% 11.69/2.05  num_of_symbols:                         51
% 11.69/2.05  num_of_terms:                           31446
% 11.69/2.05  
% 11.69/2.05  ------ Preprocessing
% 11.69/2.05  
% 11.69/2.05  num_of_splits:                          0
% 11.69/2.05  num_of_split_atoms:                     0
% 11.69/2.05  num_of_reused_defs:                     0
% 11.69/2.05  num_eq_ax_congr_red:                    28
% 11.69/2.05  num_of_sem_filtered_clauses:            1
% 11.69/2.05  num_of_subtypes:                        0
% 11.69/2.05  monotx_restored_types:                  0
% 11.69/2.05  sat_num_of_epr_types:                   0
% 11.69/2.05  sat_num_of_non_cyclic_types:            0
% 11.69/2.05  sat_guarded_non_collapsed_types:        0
% 11.69/2.05  num_pure_diseq_elim:                    0
% 11.69/2.05  simp_replaced_by:                       0
% 11.69/2.05  res_preprocessed:                       119
% 11.69/2.05  prep_upred:                             0
% 11.69/2.05  prep_unflattend:                        0
% 11.69/2.05  smt_new_axioms:                         0
% 11.69/2.05  pred_elim_cands:                        4
% 11.69/2.05  pred_elim:                              0
% 11.69/2.05  pred_elim_cl:                           0
% 11.69/2.05  pred_elim_cycles:                       1
% 11.69/2.05  merged_defs:                            12
% 11.69/2.05  merged_defs_ncl:                        0
% 11.69/2.05  bin_hyper_res:                          12
% 11.69/2.05  prep_cycles:                            3
% 11.69/2.05  pred_elim_time:                         0.
% 11.69/2.05  splitting_time:                         0.
% 11.69/2.05  sem_filter_time:                        0.
% 11.69/2.05  monotx_time:                            0.001
% 11.69/2.05  subtype_inf_time:                       0.
% 11.69/2.05  
% 11.69/2.05  ------ Problem properties
% 11.69/2.05  
% 11.69/2.05  clauses:                                34
% 11.69/2.05  conjectures:                            5
% 11.69/2.05  epr:                                    7
% 11.69/2.05  horn:                                   25
% 11.69/2.05  ground:                                 4
% 11.69/2.05  unary:                                  5
% 11.69/2.05  binary:                                 17
% 11.69/2.05  lits:                                   75
% 11.69/2.05  lits_eq:                                14
% 11.69/2.05  fd_pure:                                0
% 11.69/2.05  fd_pseudo:                              0
% 11.69/2.05  fd_cond:                                3
% 11.69/2.05  fd_pseudo_cond:                         3
% 11.69/2.05  ac_symbols:                             0
% 11.69/2.05  
% 11.69/2.05  ------ Propositional Solver
% 11.69/2.05  
% 11.69/2.05  prop_solver_calls:                      26
% 11.69/2.05  prop_fast_solver_calls:                 1636
% 11.69/2.05  smt_solver_calls:                       0
% 11.69/2.05  smt_fast_solver_calls:                  0
% 11.69/2.05  prop_num_of_clauses:                    17533
% 11.69/2.05  prop_preprocess_simplified:             29113
% 11.69/2.05  prop_fo_subsumed:                       34
% 11.69/2.05  prop_solver_time:                       0.
% 11.69/2.05  smt_solver_time:                        0.
% 11.69/2.05  smt_fast_solver_time:                   0.
% 11.69/2.05  prop_fast_solver_time:                  0.
% 11.69/2.05  prop_unsat_core_time:                   0.001
% 11.69/2.05  
% 11.69/2.05  ------ QBF
% 11.69/2.05  
% 11.69/2.05  qbf_q_res:                              0
% 11.69/2.05  qbf_num_tautologies:                    0
% 11.69/2.05  qbf_prep_cycles:                        0
% 11.69/2.05  
% 11.69/2.05  ------ BMC1
% 11.69/2.05  
% 11.69/2.05  bmc1_current_bound:                     -1
% 11.69/2.05  bmc1_last_solved_bound:                 -1
% 11.69/2.05  bmc1_unsat_core_size:                   -1
% 11.69/2.05  bmc1_unsat_core_parents_size:           -1
% 11.69/2.05  bmc1_merge_next_fun:                    0
% 11.69/2.05  bmc1_unsat_core_clauses_time:           0.
% 11.69/2.05  
% 11.69/2.05  ------ Instantiation
% 11.69/2.05  
% 11.69/2.05  inst_num_of_clauses:                    4009
% 11.69/2.05  inst_num_in_passive:                    1743
% 11.69/2.05  inst_num_in_active:                     1250
% 11.69/2.05  inst_num_in_unprocessed:                1016
% 11.69/2.05  inst_num_of_loops:                      1940
% 11.69/2.05  inst_num_of_learning_restarts:          0
% 11.69/2.05  inst_num_moves_active_passive:          688
% 11.69/2.05  inst_lit_activity:                      0
% 11.69/2.05  inst_lit_activity_moves:                0
% 11.69/2.05  inst_num_tautologies:                   0
% 11.69/2.05  inst_num_prop_implied:                  0
% 11.69/2.05  inst_num_existing_simplified:           0
% 11.69/2.05  inst_num_eq_res_simplified:             0
% 11.69/2.05  inst_num_child_elim:                    0
% 11.69/2.05  inst_num_of_dismatching_blockings:      3747
% 11.69/2.05  inst_num_of_non_proper_insts:           5251
% 11.69/2.05  inst_num_of_duplicates:                 0
% 11.69/2.05  inst_inst_num_from_inst_to_res:         0
% 11.69/2.05  inst_dismatching_checking_time:         0.
% 11.69/2.05  
% 11.69/2.05  ------ Resolution
% 11.69/2.05  
% 11.69/2.05  res_num_of_clauses:                     0
% 11.69/2.05  res_num_in_passive:                     0
% 11.69/2.05  res_num_in_active:                      0
% 11.69/2.05  res_num_of_loops:                       122
% 11.69/2.05  res_forward_subset_subsumed:            353
% 11.69/2.05  res_backward_subset_subsumed:           0
% 11.69/2.05  res_forward_subsumed:                   0
% 11.69/2.05  res_backward_subsumed:                  0
% 11.69/2.05  res_forward_subsumption_resolution:     0
% 11.69/2.05  res_backward_subsumption_resolution:    0
% 11.69/2.05  res_clause_to_clause_subsumption:       12464
% 11.69/2.05  res_orphan_elimination:                 0
% 11.69/2.05  res_tautology_del:                      329
% 11.69/2.05  res_num_eq_res_simplified:              0
% 11.69/2.05  res_num_sel_changes:                    0
% 11.69/2.05  res_moves_from_active_to_pass:          0
% 11.69/2.05  
% 11.69/2.05  ------ Superposition
% 11.69/2.05  
% 11.69/2.05  sup_time_total:                         0.
% 11.69/2.05  sup_time_generating:                    0.
% 11.69/2.05  sup_time_sim_full:                      0.
% 11.69/2.05  sup_time_sim_immed:                     0.
% 11.69/2.05  
% 11.69/2.05  sup_num_of_clauses:                     1322
% 11.69/2.05  sup_num_in_active:                      109
% 11.69/2.05  sup_num_in_passive:                     1213
% 11.69/2.05  sup_num_of_loops:                       386
% 11.69/2.05  sup_fw_superposition:                   907
% 11.69/2.05  sup_bw_superposition:                   2125
% 11.69/2.05  sup_immediate_simplified:               1390
% 11.69/2.05  sup_given_eliminated:                   2
% 11.69/2.05  comparisons_done:                       0
% 11.69/2.05  comparisons_avoided:                    180
% 11.69/2.05  
% 11.69/2.05  ------ Simplifications
% 11.69/2.05  
% 11.69/2.05  
% 11.69/2.05  sim_fw_subset_subsumed:                 646
% 11.69/2.05  sim_bw_subset_subsumed:                 174
% 11.69/2.05  sim_fw_subsumed:                        589
% 11.69/2.05  sim_bw_subsumed:                        21
% 11.69/2.05  sim_fw_subsumption_res:                 3
% 11.69/2.05  sim_bw_subsumption_res:                 1
% 11.69/2.05  sim_tautology_del:                      18
% 11.69/2.05  sim_eq_tautology_del:                   73
% 11.69/2.05  sim_eq_res_simp:                        6
% 11.69/2.05  sim_fw_demodulated:                     122
% 11.69/2.05  sim_bw_demodulated:                     239
% 11.69/2.05  sim_light_normalised:                   33
% 11.69/2.05  sim_joinable_taut:                      0
% 11.69/2.05  sim_joinable_simp:                      0
% 11.69/2.05  sim_ac_normalised:                      0
% 11.69/2.05  sim_smt_subsumption:                    0
% 11.69/2.05  
%------------------------------------------------------------------------------
