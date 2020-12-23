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
% DateTime   : Thu Dec  3 11:42:26 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :  250 (4142 expanded)
%              Number of clauses        :  166 (1254 expanded)
%              Number of leaves         :   27 ( 897 expanded)
%              Depth                    :   31
%              Number of atoms          :  710 (19092 expanded)
%              Number of equality atoms :  332 (2138 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f42])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f40])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f62,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r2_hidden(X3,X2) )
     => ( ~ r2_hidden(X1,sK8)
        & r2_hidden(sK8,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
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
            ( ~ r2_hidden(sK6,X3)
            & r2_hidden(X3,sK7) )
        | ~ r2_hidden(sK6,k8_setfam_1(sK5,sK7)) )
      & ( ! [X4] :
            ( r2_hidden(sK6,X4)
            | ~ r2_hidden(X4,sK7) )
        | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) )
      & r2_hidden(sK6,sK5)
      & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( ( ~ r2_hidden(sK6,sK8)
        & r2_hidden(sK8,sK7) )
      | ~ r2_hidden(sK6,k8_setfam_1(sK5,sK7)) )
    & ( ! [X4] :
          ( r2_hidden(sK6,X4)
          | ~ r2_hidden(X4,sK7) )
      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) )
    & r2_hidden(sK6,sK5)
    & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f60,f62,f61])).

fof(f93,plain,(
    ! [X4] :
      ( r2_hidden(sK6,X4)
      | ~ r2_hidden(X4,sK7)
      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f94,plain,
    ( r2_hidden(sK8,sK7)
    | ~ r2_hidden(sK6,k8_setfam_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f63])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_subset_1(X0,X1,X1) = X1 ) ),
    inference(rectify,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k8_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f51])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
    inference(cnf_transformation,[],[f63])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f38])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f56])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,
    ( ~ r2_hidden(sK6,sK8)
    | ~ r2_hidden(sK6,k8_setfam_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f63])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f48])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1101,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(sK6,X0)
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1079,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK6,X0) = iProver_top
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1570,plain,
    ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK6,sK0(sK7)) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_1079])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK8,sK7)
    | ~ r2_hidden(sK6,k8_setfam_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1080,plain,
    ( r2_hidden(sK8,sK7) = iProver_top
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1866,plain,
    ( r2_hidden(sK8,sK7) = iProver_top
    | r2_hidden(sK6,sK0(sK7)) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_1080])).

cnf(c_7,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1094,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_subset_1(X1,X0,X0) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_238,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_297,plain,
    ( ~ r1_tarski(X0,X1)
    | k8_subset_1(X1,X0,X0) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_239])).

cnf(c_1076,plain,
    ( k8_subset_1(X0,X1,X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_10481,plain,
    ( k8_subset_1(X0,k1_tarski(X1),k1_tarski(X1)) = k1_tarski(X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1076])).

cnf(c_15190,plain,
    ( k8_subset_1(sK0(sK7),k1_tarski(sK6),k1_tarski(sK6)) = k1_tarski(sK6)
    | r2_hidden(sK8,sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1866,c_10481])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_33,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_37,plain,
    ( r2_hidden(sK8,sK7) = iProver_top
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_394,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1737,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_1850,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_396,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1433,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6,sK5)
    | X1 != sK5
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_2243,plain,
    ( r2_hidden(sK6,k8_setfam_1(sK5,sK7))
    | ~ r2_hidden(sK6,sK5)
    | k8_setfam_1(sK5,sK7) != sK5
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1433])).

cnf(c_2244,plain,
    ( k8_setfam_1(sK5,sK7) != sK5
    | sK6 != sK6
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2243])).

cnf(c_395,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1853,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_2603,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1853])).

cnf(c_3152,plain,
    ( k8_setfam_1(sK5,k1_xboole_0) != sK5
    | sK5 = k8_setfam_1(sK5,k1_xboole_0)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_18,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3153,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK5)))
    | k8_setfam_1(sK5,k1_xboole_0) = sK5 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1384,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_7058,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK3(X1,X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_299,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK3(X1,X0),X0)
    | k1_xboole_0 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_239])).

cnf(c_8962,plain,
    ( ~ r1_tarski(sK7,X0)
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
    | r2_hidden(sK6,sK3(X0,sK7))
    | k1_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_299,c_29])).

cnf(c_9607,plain,
    ( ~ r1_tarski(sK7,X0)
    | r2_hidden(sK8,sK7)
    | r2_hidden(sK6,sK3(X0,sK7))
    | k1_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_8962,c_28])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_9621,plain,
    ( ~ r1_tarski(sK3(X0,sK7),X1)
    | ~ r1_tarski(sK7,X0)
    | r2_hidden(sK8,sK7)
    | r2_hidden(sK6,X1)
    | k1_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_9607,c_3])).

cnf(c_409,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1077,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1089,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5651,plain,
    ( k6_setfam_1(sK5,sK7) = k8_setfam_1(sK5,sK7)
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1077,c_1089])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1088,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3071,plain,
    ( k6_setfam_1(sK5,sK7) = k1_setfam_1(sK7) ),
    inference(superposition,[status(thm)],[c_1077,c_1088])).

cnf(c_5654,plain,
    ( k8_setfam_1(sK5,sK7) = k1_setfam_1(sK7)
    | sK7 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5651,c_3071])).

cnf(c_6227,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK8,sK7) = iProver_top
    | r2_hidden(sK6,k1_setfam_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5654,c_1080])).

cnf(c_6314,plain,
    ( r2_hidden(sK8,sK7)
    | ~ r2_hidden(sK6,k1_setfam_1(sK7))
    | sK7 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6227])).

cnf(c_9305,plain,
    ( X0 != X1
    | X0 = sK7
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_9306,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9305])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,sK4(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3121,plain,
    ( r1_tarski(k1_tarski(X0),k1_setfam_1(X1))
    | ~ r2_hidden(X0,sK4(X1,k1_tarski(X0)))
    | k1_xboole_0 = X1 ),
    inference(resolution,[status(thm)],[c_25,c_7])).

cnf(c_26,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK4(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3101,plain,
    ( r1_tarski(X0,k1_setfam_1(sK7))
    | r2_hidden(sK6,sK4(sK7,X0))
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
    | k1_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_26,c_29])).

cnf(c_9495,plain,
    ( r1_tarski(k1_tarski(sK6),k1_setfam_1(sK7))
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
    | k1_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_3121,c_3101])).

cnf(c_8,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_9637,plain,
    ( r2_hidden(sK6,k8_setfam_1(sK5,sK7))
    | r2_hidden(sK6,k1_setfam_1(sK7))
    | k1_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_9495,c_8])).

cnf(c_9814,plain,
    ( r2_hidden(sK8,sK7)
    | k1_xboole_0 = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9621,c_28,c_409,c_6314,c_9306,c_9637])).

cnf(c_3266,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_395,c_394])).

cnf(c_9830,plain,
    ( r2_hidden(sK8,sK7)
    | sK7 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9814,c_3266])).

cnf(c_9831,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9830])).

cnf(c_401,plain,
    ( X0 != X1
    | X2 != X3
    | k8_setfam_1(X0,X2) = k8_setfam_1(X1,X3) ),
    theory(equality)).

cnf(c_5182,plain,
    ( k8_setfam_1(sK5,sK7) = k8_setfam_1(X0,X1)
    | sK7 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_401])).

cnf(c_13173,plain,
    ( k8_setfam_1(sK5,sK7) = k8_setfam_1(sK5,X0)
    | sK7 != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_5182])).

cnf(c_13174,plain,
    ( k8_setfam_1(sK5,sK7) = k8_setfam_1(sK5,k1_xboole_0)
    | sK7 != k1_xboole_0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_13173])).

cnf(c_2641,plain,
    ( k8_setfam_1(sK5,sK7) != X0
    | k8_setfam_1(sK5,sK7) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_16730,plain,
    ( k8_setfam_1(sK5,sK7) != k8_setfam_1(sK5,k1_xboole_0)
    | k8_setfam_1(sK5,sK7) = sK5
    | sK5 != k8_setfam_1(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2641])).

cnf(c_18908,plain,
    ( r2_hidden(sK8,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15190,c_33,c_37,c_1737,c_1850,c_2244,c_3152,c_3153,c_7058,c_9831,c_13174,c_16730])).

cnf(c_1082,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK4(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3446,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(X0,k1_setfam_1(sK7)) = iProver_top
    | r2_hidden(sK6,sK4(sK7,X0)) = iProver_top
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_1079])).

cnf(c_24,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1084,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4606,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1084])).

cnf(c_4726,plain,
    ( m1_subset_1(X0,sK5) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4606,c_1084])).

cnf(c_5263,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK6,sK5) = iProver_top
    | r1_tarski(X0,k1_setfam_1(sK7)) = iProver_top
    | r2_hidden(sK4(sK7,X0),sK7) != iProver_top
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3446,c_4726])).

cnf(c_1558,plain,
    ( ~ r2_hidden(sK8,sK7)
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
    | r2_hidden(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1559,plain,
    ( r2_hidden(sK8,sK7) != iProver_top
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_2375,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5))
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_24,c_31])).

cnf(c_2428,plain,
    ( m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,sK7) ),
    inference(resolution,[status(thm)],[c_2375,c_24])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2574,plain,
    ( m1_subset_1(X0,sK5)
    | r1_tarski(sK7,X1)
    | ~ r2_hidden(X0,sK1(sK7,X1)) ),
    inference(resolution,[status(thm)],[c_2428,c_2])).

cnf(c_1506,plain,
    ( r1_tarski(sK7,X0)
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
    | r2_hidden(sK6,sK1(sK7,X0)) ),
    inference(resolution,[status(thm)],[c_2,c_29])).

cnf(c_3705,plain,
    ( m1_subset_1(sK6,sK5)
    | r1_tarski(sK7,X0)
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) ),
    inference(resolution,[status(thm)],[c_2574,c_1506])).

cnf(c_3710,plain,
    ( m1_subset_1(sK6,sK5) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3705])).

cnf(c_1074,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r2_hidden(sK3(X1,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_4177,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(sK7,X0) != iProver_top
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK6,sK3(X0,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1074,c_1079])).

cnf(c_4747,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(sK7,X0) != iProver_top
    | r2_hidden(sK8,sK7) = iProver_top
    | r2_hidden(sK6,sK3(X0,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4177,c_1080])).

cnf(c_5265,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK6,sK5) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top
    | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_4747,c_4726])).

cnf(c_1802,plain,
    ( r1_tarski(sK7,X0)
    | r2_hidden(sK8,sK7)
    | r2_hidden(sK6,sK1(sK7,X0)) ),
    inference(resolution,[status(thm)],[c_1506,c_28])).

cnf(c_3706,plain,
    ( m1_subset_1(sK6,sK5)
    | r1_tarski(sK7,X0)
    | r2_hidden(sK8,sK7) ),
    inference(resolution,[status(thm)],[c_2574,c_1802])).

cnf(c_3707,plain,
    ( m1_subset_1(sK6,sK5) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3706])).

cnf(c_9552,plain,
    ( m1_subset_1(sK6,sK5) = iProver_top
    | sK7 = k1_xboole_0
    | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5265,c_3707])).

cnf(c_9553,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK6,sK5) = iProver_top
    | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_9552])).

cnf(c_9562,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK6,sK5) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1074,c_9553])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(sK6,k8_setfam_1(sK5,sK7))
    | ~ r2_hidden(sK6,sK8) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1081,plain,
    ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4746,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(sK7,X0) != iProver_top
    | r2_hidden(sK6,sK3(X0,sK7)) = iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4177,c_1081])).

cnf(c_5264,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK6,sK5) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top
    | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4746,c_4726])).

cnf(c_1099,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2400,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK6,sK1(sK7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_1079])).

cnf(c_2502,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | r2_hidden(sK6,sK1(sK7,X0)) = iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2400,c_1081])).

cnf(c_5260,plain,
    ( m1_subset_1(sK6,sK5) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top
    | r2_hidden(sK1(sK7,X0),sK7) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2502,c_4726])).

cnf(c_38,plain,
    ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8148,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | m1_subset_1(sK6,sK5) = iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5260,c_38,c_3710])).

cnf(c_8149,plain,
    ( m1_subset_1(sK6,sK5) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_8148])).

cnf(c_9567,plain,
    ( m1_subset_1(sK6,sK5) = iProver_top
    | sK7 = k1_xboole_0
    | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5264,c_8149])).

cnf(c_9568,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK6,sK5) = iProver_top
    | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_9567])).

cnf(c_9577,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK6,sK5) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1074,c_9568])).

cnf(c_9766,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK6,sK5) = iProver_top
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5263,c_1559,c_3710,c_9562,c_9577])).

cnf(c_9777,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK6,sK5) = iProver_top
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9766,c_1080])).

cnf(c_9948,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9777,c_9831])).

cnf(c_9957,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_9948,c_1079])).

cnf(c_2814,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_9591,plain,
    ( ~ r1_tarski(sK3(X0,sK7),X1)
    | ~ r1_tarski(sK7,X0)
    | r2_hidden(sK6,X1)
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
    | k1_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_8962,c_3])).

cnf(c_6226,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK6,k1_setfam_1(sK7)) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5654,c_1081])).

cnf(c_6313,plain,
    ( ~ r2_hidden(sK6,k1_setfam_1(sK7))
    | ~ r2_hidden(sK6,sK8)
    | sK7 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6226])).

cnf(c_9854,plain,
    ( r2_hidden(sK6,k8_setfam_1(sK5,sK7))
    | k1_xboole_0 = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9591,c_409,c_1558,c_6313,c_9306,c_9637,c_9814])).

cnf(c_9856,plain,
    ( k1_xboole_0 = sK7
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9854])).

cnf(c_2817,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_10805,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2817])).

cnf(c_10806,plain,
    ( sK7 != sK7
    | sK7 = k1_xboole_0
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_10805])).

cnf(c_10844,plain,
    ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9957,c_2814,c_9856,c_10806])).

cnf(c_10845,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10844])).

cnf(c_10850,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK6,k1_setfam_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5654,c_10845])).

cnf(c_23,plain,
    ( r1_tarski(k1_setfam_1(X0),X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1085,plain,
    ( r1_tarski(k1_setfam_1(X0),X1) = iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1098,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4533,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(X2,k1_setfam_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_1098])).

cnf(c_23029,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10850,c_4533])).

cnf(c_34882,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_18908,c_23029])).

cnf(c_18920,plain,
    ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
    | r2_hidden(sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_18908,c_1079])).

cnf(c_19107,plain,
    ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18920,c_33,c_1737,c_1850,c_2244,c_3152,c_3153,c_7058,c_10845,c_13174,c_16730])).

cnf(c_35109,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34882,c_33,c_38,c_1737,c_1850,c_2244,c_3152,c_3153,c_7058,c_10845,c_13174,c_16730])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1086,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1679,plain,
    ( r1_tarski(sK7,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1086])).

cnf(c_10486,plain,
    ( k8_subset_1(k1_zfmisc_1(sK5),sK7,sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_1679,c_1076])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_subset_1(X1,X0,X2) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_298,plain,
    ( ~ r1_tarski(X0,X1)
    | k8_subset_1(X1,X0,X2) = k3_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_239])).

cnf(c_1075,plain,
    ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_12828,plain,
    ( k8_subset_1(k1_zfmisc_1(sK5),sK7,X0) = k3_xboole_0(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1679,c_1075])).

cnf(c_13073,plain,
    ( k3_xboole_0(sK7,sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_10486,c_12828])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1097,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13190,plain,
    ( r1_xboole_0(sK7,sK7) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_13073,c_1097])).

cnf(c_18917,plain,
    ( r1_xboole_0(sK7,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_18908,c_13190])).

cnf(c_35152,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35109,c_18917])).

cnf(c_3757,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3760,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3757])).

cnf(c_3762,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3760])).

cnf(c_2196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k3_subset_1(X1,X2)))
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2197,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k3_subset_1(X1,X2))) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2196])).

cnf(c_2199,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2197])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_xboole_0(X0,X2)
    | ~ r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_72,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X2,X0) = iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_74,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_66,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_68,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35152,c_3762,c_2199,c_74,c_68])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:33:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.01/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.01/1.49  
% 8.01/1.49  ------  iProver source info
% 8.01/1.49  
% 8.01/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.01/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.01/1.49  git: non_committed_changes: false
% 8.01/1.49  git: last_make_outside_of_git: false
% 8.01/1.49  
% 8.01/1.49  ------ 
% 8.01/1.49  ------ Parsing...
% 8.01/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.01/1.49  ------ Proving...
% 8.01/1.49  ------ Problem Properties 
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  clauses                                 32
% 8.01/1.49  conjectures                             5
% 8.01/1.49  EPR                                     3
% 8.01/1.49  Horn                                    23
% 8.01/1.49  unary                                   3
% 8.01/1.49  binary                                  18
% 8.01/1.49  lits                                    74
% 8.01/1.49  lits eq                                 11
% 8.01/1.49  fd_pure                                 0
% 8.01/1.49  fd_pseudo                               0
% 8.01/1.49  fd_cond                                 5
% 8.01/1.49  fd_pseudo_cond                          1
% 8.01/1.49  AC symbols                              0
% 8.01/1.49  
% 8.01/1.49  ------ Input Options Time Limit: Unbounded
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  ------ 
% 8.01/1.49  Current options:
% 8.01/1.49  ------ 
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  ------ Proving...
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  % SZS status Theorem for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  fof(f1,axiom,(
% 8.01/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f22,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 8.01/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 8.01/1.49  
% 8.01/1.49  fof(f23,plain,(
% 8.01/1.49    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f22])).
% 8.01/1.49  
% 8.01/1.49  fof(f42,plain,(
% 8.01/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f43,plain,(
% 8.01/1.49    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 8.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f42])).
% 8.01/1.49  
% 8.01/1.49  fof(f64,plain,(
% 8.01/1.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f43])).
% 8.01/1.49  
% 8.01/1.49  fof(f18,conjecture,(
% 8.01/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f19,negated_conjecture,(
% 8.01/1.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 8.01/1.49    inference(negated_conjecture,[],[f18])).
% 8.01/1.49  
% 8.01/1.49  fof(f40,plain,(
% 8.01/1.49    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.01/1.49    inference(ennf_transformation,[],[f19])).
% 8.01/1.49  
% 8.01/1.49  fof(f41,plain,(
% 8.01/1.49    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.01/1.49    inference(flattening,[],[f40])).
% 8.01/1.49  
% 8.01/1.49  fof(f58,plain,(
% 8.01/1.49    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.01/1.49    inference(nnf_transformation,[],[f41])).
% 8.01/1.49  
% 8.01/1.49  fof(f59,plain,(
% 8.01/1.49    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.01/1.49    inference(flattening,[],[f58])).
% 8.01/1.49  
% 8.01/1.49  fof(f60,plain,(
% 8.01/1.49    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.01/1.49    inference(rectify,[],[f59])).
% 8.01/1.49  
% 8.01/1.49  fof(f62,plain,(
% 8.01/1.49    ( ! [X2,X1] : (? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) => (~r2_hidden(X1,sK8) & r2_hidden(sK8,X2))) )),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f61,plain,(
% 8.01/1.49    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK6,X3) & r2_hidden(X3,sK7)) | ~r2_hidden(sK6,k8_setfam_1(sK5,sK7))) & (! [X4] : (r2_hidden(sK6,X4) | ~r2_hidden(X4,sK7)) | r2_hidden(sK6,k8_setfam_1(sK5,sK7))) & r2_hidden(sK6,sK5) & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(sK5))))),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f63,plain,(
% 8.01/1.49    ((~r2_hidden(sK6,sK8) & r2_hidden(sK8,sK7)) | ~r2_hidden(sK6,k8_setfam_1(sK5,sK7))) & (! [X4] : (r2_hidden(sK6,X4) | ~r2_hidden(X4,sK7)) | r2_hidden(sK6,k8_setfam_1(sK5,sK7))) & r2_hidden(sK6,sK5) & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(sK5)))),
% 8.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f60,f62,f61])).
% 8.01/1.49  
% 8.01/1.49  fof(f93,plain,(
% 8.01/1.49    ( ! [X4] : (r2_hidden(sK6,X4) | ~r2_hidden(X4,sK7) | r2_hidden(sK6,k8_setfam_1(sK5,sK7))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f63])).
% 8.01/1.49  
% 8.01/1.49  fof(f94,plain,(
% 8.01/1.49    r2_hidden(sK8,sK7) | ~r2_hidden(sK6,k8_setfam_1(sK5,sK7))),
% 8.01/1.49    inference(cnf_transformation,[],[f63])).
% 8.01/1.49  
% 8.01/1.49  fof(f5,axiom,(
% 8.01/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f50,plain,(
% 8.01/1.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 8.01/1.49    inference(nnf_transformation,[],[f5])).
% 8.01/1.49  
% 8.01/1.49  fof(f72,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f50])).
% 8.01/1.49  
% 8.01/1.49  fof(f6,axiom,(
% 8.01/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_subset_1(X0,X1,X1) = X1)),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f21,plain,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_subset_1(X0,X1,X1) = X1)),
% 8.01/1.49    inference(rectify,[],[f6])).
% 8.01/1.49  
% 8.01/1.49  fof(f27,plain,(
% 8.01/1.49    ! [X0,X1] : (k8_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f21])).
% 8.01/1.49  
% 8.01/1.49  fof(f73,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k8_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f27])).
% 8.01/1.49  
% 8.01/1.49  fof(f14,axiom,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f55,plain,(
% 8.01/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.01/1.49    inference(nnf_transformation,[],[f14])).
% 8.01/1.49  
% 8.01/1.49  fof(f86,plain,(
% 8.01/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f55])).
% 8.01/1.49  
% 8.01/1.49  fof(f92,plain,(
% 8.01/1.49    r2_hidden(sK6,sK5)),
% 8.01/1.49    inference(cnf_transformation,[],[f63])).
% 8.01/1.49  
% 8.01/1.49  fof(f12,axiom,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f33,plain,(
% 8.01/1.49    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.01/1.49    inference(ennf_transformation,[],[f12])).
% 8.01/1.49  
% 8.01/1.49  fof(f83,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f33])).
% 8.01/1.49  
% 8.01/1.49  fof(f97,plain,(
% 8.01/1.49    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 8.01/1.49    inference(equality_resolution,[],[f83])).
% 8.01/1.49  
% 8.01/1.49  fof(f11,axiom,(
% 8.01/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f81,plain,(
% 8.01/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f11])).
% 8.01/1.49  
% 8.01/1.49  fof(f8,axiom,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f29,plain,(
% 8.01/1.49    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f8])).
% 8.01/1.49  
% 8.01/1.49  fof(f30,plain,(
% 8.01/1.49    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.01/1.49    inference(flattening,[],[f29])).
% 8.01/1.49  
% 8.01/1.49  fof(f51,plain,(
% 8.01/1.49    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)))),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f52,plain,(
% 8.01/1.49    ! [X0,X1] : ((r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f51])).
% 8.01/1.49  
% 8.01/1.49  fof(f76,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f52])).
% 8.01/1.49  
% 8.01/1.49  fof(f2,axiom,(
% 8.01/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f24,plain,(
% 8.01/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f2])).
% 8.01/1.49  
% 8.01/1.49  fof(f44,plain,(
% 8.01/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 8.01/1.49    inference(nnf_transformation,[],[f24])).
% 8.01/1.49  
% 8.01/1.49  fof(f45,plain,(
% 8.01/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.01/1.49    inference(rectify,[],[f44])).
% 8.01/1.49  
% 8.01/1.49  fof(f46,plain,(
% 8.01/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f47,plain,(
% 8.01/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 8.01/1.49  
% 8.01/1.49  fof(f65,plain,(
% 8.01/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f47])).
% 8.01/1.49  
% 8.01/1.49  fof(f91,plain,(
% 8.01/1.49    m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(sK5)))),
% 8.01/1.49    inference(cnf_transformation,[],[f63])).
% 8.01/1.49  
% 8.01/1.49  fof(f82,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f33])).
% 8.01/1.49  
% 8.01/1.49  fof(f13,axiom,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f34,plain,(
% 8.01/1.49    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.01/1.49    inference(ennf_transformation,[],[f13])).
% 8.01/1.49  
% 8.01/1.49  fof(f84,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f34])).
% 8.01/1.49  
% 8.01/1.49  fof(f17,axiom,(
% 8.01/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f38,plain,(
% 8.01/1.49    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f17])).
% 8.01/1.49  
% 8.01/1.49  fof(f39,plain,(
% 8.01/1.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 8.01/1.49    inference(flattening,[],[f38])).
% 8.01/1.49  
% 8.01/1.49  fof(f56,plain,(
% 8.01/1.49    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f57,plain,(
% 8.01/1.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 8.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f56])).
% 8.01/1.49  
% 8.01/1.49  fof(f90,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK4(X0,X1))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f57])).
% 8.01/1.49  
% 8.01/1.49  fof(f89,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK4(X0,X1),X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f57])).
% 8.01/1.49  
% 8.01/1.49  fof(f71,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f50])).
% 8.01/1.49  
% 8.01/1.49  fof(f16,axiom,(
% 8.01/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f36,plain,(
% 8.01/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 8.01/1.49    inference(ennf_transformation,[],[f16])).
% 8.01/1.49  
% 8.01/1.49  fof(f37,plain,(
% 8.01/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 8.01/1.49    inference(flattening,[],[f36])).
% 8.01/1.49  
% 8.01/1.49  fof(f88,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f37])).
% 8.01/1.49  
% 8.01/1.49  fof(f66,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f47])).
% 8.01/1.49  
% 8.01/1.49  fof(f95,plain,(
% 8.01/1.49    ~r2_hidden(sK6,sK8) | ~r2_hidden(sK6,k8_setfam_1(sK5,sK7))),
% 8.01/1.49    inference(cnf_transformation,[],[f63])).
% 8.01/1.49  
% 8.01/1.49  fof(f15,axiom,(
% 8.01/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f35,plain,(
% 8.01/1.49    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 8.01/1.49    inference(ennf_transformation,[],[f15])).
% 8.01/1.49  
% 8.01/1.49  fof(f87,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f35])).
% 8.01/1.49  
% 8.01/1.49  fof(f85,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f55])).
% 8.01/1.49  
% 8.01/1.49  fof(f7,axiom,(
% 8.01/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f28,plain,(
% 8.01/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f7])).
% 8.01/1.49  
% 8.01/1.49  fof(f74,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f28])).
% 8.01/1.49  
% 8.01/1.49  fof(f3,axiom,(
% 8.01/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f20,plain,(
% 8.01/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 8.01/1.49    inference(rectify,[],[f3])).
% 8.01/1.49  
% 8.01/1.49  fof(f25,plain,(
% 8.01/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 8.01/1.49    inference(ennf_transformation,[],[f20])).
% 8.01/1.49  
% 8.01/1.49  fof(f48,plain,(
% 8.01/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f49,plain,(
% 8.01/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 8.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f48])).
% 8.01/1.49  
% 8.01/1.49  fof(f69,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f49])).
% 8.01/1.49  
% 8.01/1.49  fof(f10,axiom,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f32,plain,(
% 8.01/1.49    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f10])).
% 8.01/1.49  
% 8.01/1.49  fof(f54,plain,(
% 8.01/1.49    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.01/1.49    inference(nnf_transformation,[],[f32])).
% 8.01/1.49  
% 8.01/1.49  fof(f80,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f54])).
% 8.01/1.49  
% 8.01/1.49  cnf(c_0,plain,
% 8.01/1.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f64]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1101,plain,
% 8.01/1.49      ( r2_hidden(sK0(X0),X0) = iProver_top
% 8.01/1.49      | v1_xboole_0(X0) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_29,negated_conjecture,
% 8.01/1.49      ( ~ r2_hidden(X0,sK7)
% 8.01/1.49      | r2_hidden(sK6,X0)
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f93]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1079,plain,
% 8.01/1.49      ( r2_hidden(X0,sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,X0) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1570,plain,
% 8.01/1.49      ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK0(sK7)) = iProver_top
% 8.01/1.49      | v1_xboole_0(sK7) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1101,c_1079]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_28,negated_conjecture,
% 8.01/1.49      ( r2_hidden(sK8,sK7) | ~ r2_hidden(sK6,k8_setfam_1(sK5,sK7)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f94]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1080,plain,
% 8.01/1.49      ( r2_hidden(sK8,sK7) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1866,plain,
% 8.01/1.49      ( r2_hidden(sK8,sK7) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK0(sK7)) = iProver_top
% 8.01/1.49      | v1_xboole_0(sK7) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1570,c_1080]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7,plain,
% 8.01/1.49      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f72]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1094,plain,
% 8.01/1.49      ( r1_tarski(k1_tarski(X0),X1) = iProver_top
% 8.01/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k8_subset_1(X1,X0,X0) = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f73]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_21,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f86]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_238,plain,
% 8.01/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.01/1.49      inference(prop_impl,[status(thm)],[c_21]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_239,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_238]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_297,plain,
% 8.01/1.49      ( ~ r1_tarski(X0,X1) | k8_subset_1(X1,X0,X0) = X0 ),
% 8.01/1.49      inference(bin_hyper_res,[status(thm)],[c_9,c_239]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1076,plain,
% 8.01/1.49      ( k8_subset_1(X0,X1,X1) = X1 | r1_tarski(X1,X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10481,plain,
% 8.01/1.49      ( k8_subset_1(X0,k1_tarski(X1),k1_tarski(X1)) = k1_tarski(X1)
% 8.01/1.49      | r2_hidden(X1,X0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1094,c_1076]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_15190,plain,
% 8.01/1.49      ( k8_subset_1(sK0(sK7),k1_tarski(sK6),k1_tarski(sK6)) = k1_tarski(sK6)
% 8.01/1.49      | r2_hidden(sK8,sK7) = iProver_top
% 8.01/1.49      | v1_xboole_0(sK7) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1866,c_10481]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_30,negated_conjecture,
% 8.01/1.49      ( r2_hidden(sK6,sK5) ),
% 8.01/1.49      inference(cnf_transformation,[],[f92]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_33,plain,
% 8.01/1.49      ( r2_hidden(sK6,sK5) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_37,plain,
% 8.01/1.49      ( r2_hidden(sK8,sK7) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_394,plain,( X0 = X0 ),theory(equality) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1737,plain,
% 8.01/1.49      ( sK6 = sK6 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_394]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1850,plain,
% 8.01/1.49      ( sK5 = sK5 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_394]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_396,plain,
% 8.01/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.01/1.49      theory(equality) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1433,plain,
% 8.01/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(sK6,sK5) | X1 != sK5 | X0 != sK6 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_396]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2243,plain,
% 8.01/1.49      ( r2_hidden(sK6,k8_setfam_1(sK5,sK7))
% 8.01/1.49      | ~ r2_hidden(sK6,sK5)
% 8.01/1.49      | k8_setfam_1(sK5,sK7) != sK5
% 8.01/1.49      | sK6 != sK6 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_1433]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2244,plain,
% 8.01/1.49      ( k8_setfam_1(sK5,sK7) != sK5
% 8.01/1.49      | sK6 != sK6
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK5) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_2243]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_395,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1853,plain,
% 8.01/1.49      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_395]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2603,plain,
% 8.01/1.49      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_1853]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3152,plain,
% 8.01/1.49      ( k8_setfam_1(sK5,k1_xboole_0) != sK5
% 8.01/1.49      | sK5 = k8_setfam_1(sK5,k1_xboole_0)
% 8.01/1.49      | sK5 != sK5 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_2603]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_18,plain,
% 8.01/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 8.01/1.49      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f97]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3153,plain,
% 8.01/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK5)))
% 8.01/1.49      | k8_setfam_1(sK5,k1_xboole_0) = sK5 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_17,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f81]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1384,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7058,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_1384]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_11,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.01/1.49      | r2_hidden(sK3(X1,X0),X0)
% 8.01/1.49      | k1_xboole_0 = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f76]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_299,plain,
% 8.01/1.49      ( ~ r1_tarski(X0,X1)
% 8.01/1.49      | r2_hidden(sK3(X1,X0),X0)
% 8.01/1.49      | k1_xboole_0 = X0 ),
% 8.01/1.49      inference(bin_hyper_res,[status(thm)],[c_11,c_239]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_8962,plain,
% 8.01/1.49      ( ~ r1_tarski(sK7,X0)
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
% 8.01/1.49      | r2_hidden(sK6,sK3(X0,sK7))
% 8.01/1.49      | k1_xboole_0 = sK7 ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_299,c_29]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9607,plain,
% 8.01/1.49      ( ~ r1_tarski(sK7,X0)
% 8.01/1.49      | r2_hidden(sK8,sK7)
% 8.01/1.49      | r2_hidden(sK6,sK3(X0,sK7))
% 8.01/1.49      | k1_xboole_0 = sK7 ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_8962,c_28]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3,plain,
% 8.01/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f65]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9621,plain,
% 8.01/1.49      ( ~ r1_tarski(sK3(X0,sK7),X1)
% 8.01/1.49      | ~ r1_tarski(sK7,X0)
% 8.01/1.49      | r2_hidden(sK8,sK7)
% 8.01/1.49      | r2_hidden(sK6,X1)
% 8.01/1.49      | k1_xboole_0 = sK7 ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_9607,c_3]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_409,plain,
% 8.01/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_394]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_31,negated_conjecture,
% 8.01/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
% 8.01/1.49      inference(cnf_transformation,[],[f91]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1077,plain,
% 8.01/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(sK5))) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_19,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 8.01/1.49      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 8.01/1.49      | k1_xboole_0 = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f82]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1089,plain,
% 8.01/1.49      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 8.01/1.49      | k1_xboole_0 = X1
% 8.01/1.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5651,plain,
% 8.01/1.49      ( k6_setfam_1(sK5,sK7) = k8_setfam_1(sK5,sK7) | sK7 = k1_xboole_0 ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1077,c_1089]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_20,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 8.01/1.49      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f84]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1088,plain,
% 8.01/1.49      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 8.01/1.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3071,plain,
% 8.01/1.49      ( k6_setfam_1(sK5,sK7) = k1_setfam_1(sK7) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1077,c_1088]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5654,plain,
% 8.01/1.49      ( k8_setfam_1(sK5,sK7) = k1_setfam_1(sK7) | sK7 = k1_xboole_0 ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_5651,c_3071]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_6227,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | r2_hidden(sK8,sK7) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,k1_setfam_1(sK7)) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_5654,c_1080]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_6314,plain,
% 8.01/1.49      ( r2_hidden(sK8,sK7)
% 8.01/1.49      | ~ r2_hidden(sK6,k1_setfam_1(sK7))
% 8.01/1.49      | sK7 = k1_xboole_0 ),
% 8.01/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_6227]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9305,plain,
% 8.01/1.49      ( X0 != X1 | X0 = sK7 | sK7 != X1 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_395]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9306,plain,
% 8.01/1.49      ( sK7 != k1_xboole_0
% 8.01/1.49      | k1_xboole_0 = sK7
% 8.01/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_9305]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_25,plain,
% 8.01/1.49      ( ~ r1_tarski(X0,sK4(X1,X0))
% 8.01/1.49      | r1_tarski(X0,k1_setfam_1(X1))
% 8.01/1.49      | k1_xboole_0 = X1 ),
% 8.01/1.49      inference(cnf_transformation,[],[f90]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3121,plain,
% 8.01/1.49      ( r1_tarski(k1_tarski(X0),k1_setfam_1(X1))
% 8.01/1.49      | ~ r2_hidden(X0,sK4(X1,k1_tarski(X0)))
% 8.01/1.49      | k1_xboole_0 = X1 ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_25,c_7]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_26,plain,
% 8.01/1.49      ( r1_tarski(X0,k1_setfam_1(X1))
% 8.01/1.49      | r2_hidden(sK4(X1,X0),X1)
% 8.01/1.49      | k1_xboole_0 = X1 ),
% 8.01/1.49      inference(cnf_transformation,[],[f89]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3101,plain,
% 8.01/1.49      ( r1_tarski(X0,k1_setfam_1(sK7))
% 8.01/1.49      | r2_hidden(sK6,sK4(sK7,X0))
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
% 8.01/1.49      | k1_xboole_0 = sK7 ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_26,c_29]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9495,plain,
% 8.01/1.49      ( r1_tarski(k1_tarski(sK6),k1_setfam_1(sK7))
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
% 8.01/1.49      | k1_xboole_0 = sK7 ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_3121,c_3101]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_8,plain,
% 8.01/1.49      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f71]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9637,plain,
% 8.01/1.49      ( r2_hidden(sK6,k8_setfam_1(sK5,sK7))
% 8.01/1.49      | r2_hidden(sK6,k1_setfam_1(sK7))
% 8.01/1.49      | k1_xboole_0 = sK7 ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_9495,c_8]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9814,plain,
% 8.01/1.49      ( r2_hidden(sK8,sK7) | k1_xboole_0 = sK7 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_9621,c_28,c_409,c_6314,c_9306,c_9637]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3266,plain,
% 8.01/1.49      ( X0 != X1 | X1 = X0 ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_395,c_394]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9830,plain,
% 8.01/1.49      ( r2_hidden(sK8,sK7) | sK7 = k1_xboole_0 ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_9814,c_3266]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9831,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0 | r2_hidden(sK8,sK7) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_9830]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_401,plain,
% 8.01/1.49      ( X0 != X1 | X2 != X3 | k8_setfam_1(X0,X2) = k8_setfam_1(X1,X3) ),
% 8.01/1.49      theory(equality) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5182,plain,
% 8.01/1.49      ( k8_setfam_1(sK5,sK7) = k8_setfam_1(X0,X1)
% 8.01/1.49      | sK7 != X1
% 8.01/1.49      | sK5 != X0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_401]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13173,plain,
% 8.01/1.49      ( k8_setfam_1(sK5,sK7) = k8_setfam_1(sK5,X0)
% 8.01/1.49      | sK7 != X0
% 8.01/1.49      | sK5 != sK5 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_5182]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13174,plain,
% 8.01/1.49      ( k8_setfam_1(sK5,sK7) = k8_setfam_1(sK5,k1_xboole_0)
% 8.01/1.49      | sK7 != k1_xboole_0
% 8.01/1.49      | sK5 != sK5 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_13173]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2641,plain,
% 8.01/1.49      ( k8_setfam_1(sK5,sK7) != X0
% 8.01/1.49      | k8_setfam_1(sK5,sK7) = sK5
% 8.01/1.49      | sK5 != X0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_395]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_16730,plain,
% 8.01/1.49      ( k8_setfam_1(sK5,sK7) != k8_setfam_1(sK5,k1_xboole_0)
% 8.01/1.49      | k8_setfam_1(sK5,sK7) = sK5
% 8.01/1.49      | sK5 != k8_setfam_1(sK5,k1_xboole_0) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_2641]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_18908,plain,
% 8.01/1.49      ( r2_hidden(sK8,sK7) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_15190,c_33,c_37,c_1737,c_1850,c_2244,c_3152,c_3153,
% 8.01/1.49                 c_7058,c_9831,c_13174,c_16730]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1082,plain,
% 8.01/1.49      ( k1_xboole_0 = X0
% 8.01/1.49      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
% 8.01/1.49      | r2_hidden(sK4(X0,X1),X0) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3446,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | r1_tarski(X0,k1_setfam_1(sK7)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK4(sK7,X0)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1082,c_1079]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_24,plain,
% 8.01/1.49      ( m1_subset_1(X0,X1)
% 8.01/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 8.01/1.49      | ~ r2_hidden(X0,X2) ),
% 8.01/1.49      inference(cnf_transformation,[],[f88]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1084,plain,
% 8.01/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 8.01/1.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 8.01/1.49      | r2_hidden(X0,X2) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4606,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(sK5)) = iProver_top
% 8.01/1.49      | r2_hidden(X0,sK7) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1077,c_1084]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4726,plain,
% 8.01/1.49      ( m1_subset_1(X0,sK5) = iProver_top
% 8.01/1.49      | r2_hidden(X0,X1) != iProver_top
% 8.01/1.49      | r2_hidden(X1,sK7) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_4606,c_1084]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5263,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r1_tarski(X0,k1_setfam_1(sK7)) = iProver_top
% 8.01/1.49      | r2_hidden(sK4(sK7,X0),sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_3446,c_4726]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1558,plain,
% 8.01/1.49      ( ~ r2_hidden(sK8,sK7)
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
% 8.01/1.49      | r2_hidden(sK6,sK8) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_29]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1559,plain,
% 8.01/1.49      ( r2_hidden(sK8,sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1558]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2375,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(sK5)) | ~ r2_hidden(X0,sK7) ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_24,c_31]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2428,plain,
% 8.01/1.49      ( m1_subset_1(X0,sK5) | ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,sK7) ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_2375,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2,plain,
% 8.01/1.49      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f66]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2574,plain,
% 8.01/1.49      ( m1_subset_1(X0,sK5)
% 8.01/1.49      | r1_tarski(sK7,X1)
% 8.01/1.49      | ~ r2_hidden(X0,sK1(sK7,X1)) ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_2428,c_2]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1506,plain,
% 8.01/1.49      ( r1_tarski(sK7,X0)
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
% 8.01/1.49      | r2_hidden(sK6,sK1(sK7,X0)) ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_2,c_29]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3705,plain,
% 8.01/1.49      ( m1_subset_1(sK6,sK5)
% 8.01/1.49      | r1_tarski(sK7,X0)
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_2574,c_1506]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3710,plain,
% 8.01/1.49      ( m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r1_tarski(sK7,X0) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_3705]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1074,plain,
% 8.01/1.49      ( k1_xboole_0 = X0
% 8.01/1.49      | r1_tarski(X0,X1) != iProver_top
% 8.01/1.49      | r2_hidden(sK3(X1,X0),X0) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4177,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | r1_tarski(sK7,X0) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK3(X0,sK7)) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1074,c_1079]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4747,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | r1_tarski(sK7,X0) != iProver_top
% 8.01/1.49      | r2_hidden(sK8,sK7) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK3(X0,sK7)) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_4177,c_1080]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5265,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r1_tarski(sK7,X0) != iProver_top
% 8.01/1.49      | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK8,sK7) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_4747,c_4726]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1802,plain,
% 8.01/1.49      ( r1_tarski(sK7,X0)
% 8.01/1.49      | r2_hidden(sK8,sK7)
% 8.01/1.49      | r2_hidden(sK6,sK1(sK7,X0)) ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_1506,c_28]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3706,plain,
% 8.01/1.49      ( m1_subset_1(sK6,sK5) | r1_tarski(sK7,X0) | r2_hidden(sK8,sK7) ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_2574,c_1802]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3707,plain,
% 8.01/1.49      ( m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r1_tarski(sK7,X0) = iProver_top
% 8.01/1.49      | r2_hidden(sK8,sK7) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_3706]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9552,plain,
% 8.01/1.49      ( m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | sK7 = k1_xboole_0
% 8.01/1.49      | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK8,sK7) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_5265,c_3707]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9553,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK8,sK7) = iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_9552]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9562,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r1_tarski(sK7,X0) != iProver_top
% 8.01/1.49      | r2_hidden(sK8,sK7) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1074,c_9553]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_27,negated_conjecture,
% 8.01/1.49      ( ~ r2_hidden(sK6,k8_setfam_1(sK5,sK7)) | ~ r2_hidden(sK6,sK8) ),
% 8.01/1.49      inference(cnf_transformation,[],[f95]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1081,plain,
% 8.01/1.49      ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4746,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | r1_tarski(sK7,X0) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK3(X0,sK7)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_4177,c_1081]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5264,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r1_tarski(sK7,X0) != iProver_top
% 8.01/1.49      | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_4746,c_4726]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1099,plain,
% 8.01/1.49      ( r1_tarski(X0,X1) = iProver_top
% 8.01/1.49      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2400,plain,
% 8.01/1.49      ( r1_tarski(sK7,X0) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK1(sK7,X0)) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1099,c_1079]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2502,plain,
% 8.01/1.49      ( r1_tarski(sK7,X0) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK1(sK7,X0)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_2400,c_1081]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5260,plain,
% 8.01/1.49      ( m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r1_tarski(sK7,X0) = iProver_top
% 8.01/1.49      | r2_hidden(sK1(sK7,X0),sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_2502,c_4726]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_38,plain,
% 8.01/1.49      ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_8148,plain,
% 8.01/1.49      ( r1_tarski(sK7,X0) = iProver_top
% 8.01/1.49      | m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_5260,c_38,c_3710]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_8149,plain,
% 8.01/1.49      ( m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r1_tarski(sK7,X0) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_8148]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9567,plain,
% 8.01/1.49      ( m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | sK7 = k1_xboole_0
% 8.01/1.49      | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_5264,c_8149]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9568,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r2_hidden(sK3(X0,sK7),sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_9567]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9577,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r1_tarski(sK7,X0) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1074,c_9568]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9766,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_5263,c_1559,c_3710,c_9562,c_9577]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9777,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | m1_subset_1(sK6,sK5) = iProver_top
% 8.01/1.49      | r2_hidden(sK8,sK7) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_9766,c_1080]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9948,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0 | r2_hidden(sK8,sK7) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_9777,c_9831]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9957,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_9948,c_1079]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2814,plain,
% 8.01/1.49      ( sK7 = sK7 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_394]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9591,plain,
% 8.01/1.49      ( ~ r1_tarski(sK3(X0,sK7),X1)
% 8.01/1.49      | ~ r1_tarski(sK7,X0)
% 8.01/1.49      | r2_hidden(sK6,X1)
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7))
% 8.01/1.49      | k1_xboole_0 = sK7 ),
% 8.01/1.49      inference(resolution,[status(thm)],[c_8962,c_3]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_6226,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | r2_hidden(sK6,k1_setfam_1(sK7)) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_5654,c_1081]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_6313,plain,
% 8.01/1.49      ( ~ r2_hidden(sK6,k1_setfam_1(sK7))
% 8.01/1.49      | ~ r2_hidden(sK6,sK8)
% 8.01/1.49      | sK7 = k1_xboole_0 ),
% 8.01/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_6226]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9854,plain,
% 8.01/1.49      ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) | k1_xboole_0 = sK7 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_9591,c_409,c_1558,c_6313,c_9306,c_9637,c_9814]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9856,plain,
% 8.01/1.49      ( k1_xboole_0 = sK7
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_9854]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2817,plain,
% 8.01/1.49      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_395]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10805,plain,
% 8.01/1.49      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_2817]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10806,plain,
% 8.01/1.49      ( sK7 != sK7 | sK7 = k1_xboole_0 | k1_xboole_0 != sK7 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_10805]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10844,plain,
% 8.01/1.49      ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
% 8.01/1.49      | sK7 = k1_xboole_0 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_9957,c_2814,c_9856,c_10806]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10845,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_10844]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10850,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | r2_hidden(sK6,k1_setfam_1(sK7)) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_5654,c_10845]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_23,plain,
% 8.01/1.49      ( r1_tarski(k1_setfam_1(X0),X1) | ~ r2_hidden(X1,X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f87]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1085,plain,
% 8.01/1.49      ( r1_tarski(k1_setfam_1(X0),X1) = iProver_top
% 8.01/1.49      | r2_hidden(X1,X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1098,plain,
% 8.01/1.49      ( r1_tarski(X0,X1) != iProver_top
% 8.01/1.49      | r2_hidden(X2,X0) != iProver_top
% 8.01/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4533,plain,
% 8.01/1.49      ( r2_hidden(X0,X1) != iProver_top
% 8.01/1.49      | r2_hidden(X2,X0) = iProver_top
% 8.01/1.49      | r2_hidden(X2,k1_setfam_1(X1)) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1085,c_1098]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_23029,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0
% 8.01/1.49      | r2_hidden(X0,sK7) != iProver_top
% 8.01/1.49      | r2_hidden(sK6,X0) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_10850,c_4533]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_34882,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0 | r2_hidden(sK6,sK8) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_18908,c_23029]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_18920,plain,
% 8.01/1.49      ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top
% 8.01/1.49      | r2_hidden(sK6,sK8) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_18908,c_1079]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_19107,plain,
% 8.01/1.49      ( r2_hidden(sK6,k8_setfam_1(sK5,sK7)) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_18920,c_33,c_1737,c_1850,c_2244,c_3152,c_3153,c_7058,
% 8.01/1.49                 c_10845,c_13174,c_16730]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_35109,plain,
% 8.01/1.49      ( sK7 = k1_xboole_0 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_34882,c_33,c_38,c_1737,c_1850,c_2244,c_3152,c_3153,
% 8.01/1.49                 c_7058,c_10845,c_13174,c_16730]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_22,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f85]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1086,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.01/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1679,plain,
% 8.01/1.49      ( r1_tarski(sK7,k1_zfmisc_1(sK5)) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1077,c_1086]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10486,plain,
% 8.01/1.49      ( k8_subset_1(k1_zfmisc_1(sK5),sK7,sK7) = sK7 ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1679,c_1076]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.01/1.49      | k8_subset_1(X1,X0,X2) = k3_xboole_0(X0,X2) ),
% 8.01/1.49      inference(cnf_transformation,[],[f74]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_298,plain,
% 8.01/1.49      ( ~ r1_tarski(X0,X1) | k8_subset_1(X1,X0,X2) = k3_xboole_0(X0,X2) ),
% 8.01/1.49      inference(bin_hyper_res,[status(thm)],[c_10,c_239]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1075,plain,
% 8.01/1.49      ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 8.01/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_12828,plain,
% 8.01/1.49      ( k8_subset_1(k1_zfmisc_1(sK5),sK7,X0) = k3_xboole_0(sK7,X0) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1679,c_1075]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13073,plain,
% 8.01/1.49      ( k3_xboole_0(sK7,sK7) = sK7 ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_10486,c_12828]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4,plain,
% 8.01/1.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f69]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1097,plain,
% 8.01/1.49      ( r1_xboole_0(X0,X1) != iProver_top
% 8.01/1.49      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13190,plain,
% 8.01/1.49      ( r1_xboole_0(sK7,sK7) != iProver_top
% 8.01/1.49      | r2_hidden(X0,sK7) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_13073,c_1097]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_18917,plain,
% 8.01/1.49      ( r1_xboole_0(sK7,sK7) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_18908,c_13190]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_35152,plain,
% 8.01/1.49      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 8.01/1.49      inference(demodulation,[status(thm)],[c_35109,c_18917]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3757,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(X0,X1))) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3760,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(X0,X1))) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_3757]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3762,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_3760]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2196,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k3_subset_1(X1,X2)))
% 8.01/1.49      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2197,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k3_subset_1(X1,X2))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_2196]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2199,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_2197]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_15,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.01/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 8.01/1.49      | r1_xboole_0(X0,X2)
% 8.01/1.49      | ~ r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f80]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_72,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.01/1.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 8.01/1.49      | r1_xboole_0(X2,X0) = iProver_top
% 8.01/1.49      | r1_tarski(X2,k3_subset_1(X1,X0)) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_74,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 8.01/1.49      | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top
% 8.01/1.49      | r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_72]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_66,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_68,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_66]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(contradiction,plain,
% 8.01/1.49      ( $false ),
% 8.01/1.49      inference(minisat,[status(thm)],[c_35152,c_3762,c_2199,c_74,c_68]) ).
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  ------                               Statistics
% 8.01/1.49  
% 8.01/1.49  ------ Selected
% 8.01/1.49  
% 8.01/1.49  total_time:                             0.892
% 8.01/1.49  
%------------------------------------------------------------------------------
