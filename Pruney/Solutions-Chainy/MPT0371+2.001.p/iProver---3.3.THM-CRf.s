%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:03 EST 2020

% Result     : Theorem 19.19s
% Output     : CNFRefutation 19.19s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 221 expanded)
%              Number of clauses        :   62 (  73 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  387 (1056 expanded)
%              Number of equality atoms :   60 ( 120 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f21])).

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
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f37])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( ~ r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( ~ r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK9) != X1
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X3,sK9) )
              & ( r2_hidden(X3,sK9)
                | r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK9,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK7,X2) != sK8
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,sK8)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK8) ) )
              | ~ m1_subset_1(X3,sK7) )
          & m1_subset_1(X2,k1_zfmisc_1(sK7)) )
      & m1_subset_1(sK8,k1_zfmisc_1(sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( k3_subset_1(sK7,sK9) != sK8
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK8)
            | ~ r2_hidden(X3,sK9) )
          & ( r2_hidden(X3,sK9)
            | r2_hidden(X3,sK8) ) )
        | ~ m1_subset_1(X3,sK7) )
    & m1_subset_1(sK9,k1_zfmisc_1(sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f56,f58,f57])).

fof(f100,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK8)
      | ~ r2_hidden(X3,sK9)
      | ~ m1_subset_1(X3,sK7) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(sK7)) ),
    inference(cnf_transformation,[],[f59])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK9)
      | r2_hidden(X3,sK8)
      | ~ m1_subset_1(X3,sK7) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f101,plain,(
    k3_subset_1(sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f59])).

fof(f98,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(sK7)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_78272,plain,
    ( r2_hidden(sK0(k3_subset_1(sK7,sK9),X0),k3_subset_1(sK7,sK9))
    | r1_tarski(k3_subset_1(sK7,sK9),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_80115,plain,
    ( r2_hidden(sK0(k3_subset_1(sK7,sK9),k3_subset_1(sK7,sK9)),k3_subset_1(sK7,sK9))
    | r1_tarski(k3_subset_1(sK7,sK9),k3_subset_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_78272])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_78271,plain,
    ( ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),X0),X0)
    | r1_tarski(k3_subset_1(sK7,sK9),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_80114,plain,
    ( ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),k3_subset_1(sK7,sK9)),k3_subset_1(sK7,sK9))
    | r1_tarski(k3_subset_1(sK7,sK9),k3_subset_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_78271])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_xboole_0(X0,X2)
    | ~ r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_12186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(X1))
    | r1_xboole_0(X0,sK9)
    | ~ r1_tarski(X0,k3_subset_1(X1,sK9)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_33996,plain,
    ( ~ m1_subset_1(k3_subset_1(sK7,sK9),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(X0))
    | r1_xboole_0(k3_subset_1(sK7,sK9),sK9)
    | ~ r1_tarski(k3_subset_1(sK7,sK9),k3_subset_1(X0,sK9)) ),
    inference(instantiation,[status(thm)],[c_12186])).

cnf(c_64992,plain,
    ( ~ m1_subset_1(k3_subset_1(sK7,sK9),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(sK7))
    | r1_xboole_0(k3_subset_1(sK7,sK9),sK9)
    | ~ r1_tarski(k3_subset_1(sK7,sK9),k3_subset_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_33996])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1797,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1796,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1782,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_36,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ r2_hidden(X0,sK8)
    | ~ r2_hidden(X0,sK9) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1771,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4931,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1782,c_1771])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK7)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_40,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_45,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_23,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_230,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_9])).

cnf(c_231,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_230])).

cnf(c_1855,plain,
    ( m1_subset_1(X0,sK7)
    | ~ r2_hidden(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_1856,plain,
    ( m1_subset_1(X0,sK7) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1855])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1929,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,sK7) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2293,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK7))
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_1929])).

cnf(c_2294,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2293])).

cnf(c_5573,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4931,c_40,c_45,c_1856,c_2294])).

cnf(c_5581,plain,
    ( r1_xboole_0(sK8,X0) = iProver_top
    | r2_hidden(sK1(sK8,X0),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_5573])).

cnf(c_5940,plain,
    ( r1_xboole_0(sK8,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_5581])).

cnf(c_5941,plain,
    ( r1_xboole_0(sK8,sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5940])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2210,plain,
    ( ~ r1_xboole_0(k3_subset_1(sK7,sK9),X0)
    | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),X0)
    | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),k3_subset_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5757,plain,
    ( ~ r1_xboole_0(k3_subset_1(sK7,sK9),sK9)
    | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),k3_subset_1(sK7,sK9))
    | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK9) ),
    inference(instantiation,[status(thm)],[c_2210])).

cnf(c_37,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | r2_hidden(X0,sK8)
    | r2_hidden(X0,sK9) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5755,plain,
    ( ~ m1_subset_1(sK0(k3_subset_1(sK7,sK9),sK8),sK7)
    | r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK8)
    | r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK9) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_5710,plain,
    ( m1_subset_1(sK0(k3_subset_1(sK7,sK9),sK8),sK7)
    | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3119,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
    | m1_subset_1(k3_subset_1(sK7,X0),k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_5020,plain,
    ( m1_subset_1(k3_subset_1(sK7,sK9),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_3119])).

cnf(c_2311,plain,
    ( ~ m1_subset_1(k3_subset_1(sK7,X0),k1_zfmisc_1(sK7))
    | ~ r2_hidden(X1,k3_subset_1(sK7,X0))
    | r2_hidden(X1,sK7) ),
    inference(instantiation,[status(thm)],[c_1929])).

cnf(c_4337,plain,
    ( ~ m1_subset_1(k3_subset_1(sK7,sK9),k1_zfmisc_1(sK7))
    | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),k3_subset_1(sK7,sK9))
    | r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_2311])).

cnf(c_1049,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3085,plain,
    ( k3_subset_1(sK7,sK9) = k3_subset_1(sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_1050,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1852,plain,
    ( k3_subset_1(sK7,sK9) != X0
    | k3_subset_1(sK7,sK9) = sK8
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_2611,plain,
    ( k3_subset_1(sK7,sK9) != k3_subset_1(sK7,sK9)
    | k3_subset_1(sK7,sK9) = sK8
    | sK8 != k3_subset_1(sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_1852])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1916,plain,
    ( ~ r1_tarski(X0,sK8)
    | ~ r1_tarski(sK8,X0)
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2066,plain,
    ( ~ r1_tarski(k3_subset_1(sK7,sK9),sK8)
    | ~ r1_tarski(sK8,k3_subset_1(sK7,sK9))
    | sK8 = k3_subset_1(sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X0,X2)
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2024,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(sK7))
    | ~ r1_xboole_0(sK8,sK9)
    | r1_tarski(sK8,k3_subset_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_1892,plain,
    ( ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK8)
    | r1_tarski(k3_subset_1(sK7,sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1893,plain,
    ( r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),k3_subset_1(sK7,sK9))
    | r1_tarski(k3_subset_1(sK7,sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_35,negated_conjecture,
    ( k3_subset_1(sK7,sK9) != sK8 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(sK7)) ),
    inference(cnf_transformation,[],[f98])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_80115,c_80114,c_64992,c_5941,c_5757,c_5755,c_5710,c_5020,c_4337,c_3085,c_2611,c_2066,c_2024,c_1892,c_1893,c_35,c_38,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.19/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.19/3.00  
% 19.19/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.19/3.00  
% 19.19/3.00  ------  iProver source info
% 19.19/3.00  
% 19.19/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.19/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.19/3.00  git: non_committed_changes: false
% 19.19/3.00  git: last_make_outside_of_git: false
% 19.19/3.00  
% 19.19/3.00  ------ 
% 19.19/3.00  
% 19.19/3.00  ------ Input Options
% 19.19/3.00  
% 19.19/3.00  --out_options                           all
% 19.19/3.00  --tptp_safe_out                         true
% 19.19/3.00  --problem_path                          ""
% 19.19/3.00  --include_path                          ""
% 19.19/3.00  --clausifier                            res/vclausify_rel
% 19.19/3.00  --clausifier_options                    ""
% 19.19/3.00  --stdin                                 false
% 19.19/3.00  --stats_out                             all
% 19.19/3.00  
% 19.19/3.00  ------ General Options
% 19.19/3.00  
% 19.19/3.00  --fof                                   false
% 19.19/3.00  --time_out_real                         305.
% 19.19/3.00  --time_out_virtual                      -1.
% 19.19/3.00  --symbol_type_check                     false
% 19.19/3.00  --clausify_out                          false
% 19.19/3.00  --sig_cnt_out                           false
% 19.19/3.00  --trig_cnt_out                          false
% 19.19/3.00  --trig_cnt_out_tolerance                1.
% 19.19/3.00  --trig_cnt_out_sk_spl                   false
% 19.19/3.00  --abstr_cl_out                          false
% 19.19/3.00  
% 19.19/3.00  ------ Global Options
% 19.19/3.00  
% 19.19/3.00  --schedule                              default
% 19.19/3.00  --add_important_lit                     false
% 19.19/3.00  --prop_solver_per_cl                    1000
% 19.19/3.00  --min_unsat_core                        false
% 19.19/3.00  --soft_assumptions                      false
% 19.19/3.00  --soft_lemma_size                       3
% 19.19/3.00  --prop_impl_unit_size                   0
% 19.19/3.00  --prop_impl_unit                        []
% 19.19/3.00  --share_sel_clauses                     true
% 19.19/3.00  --reset_solvers                         false
% 19.19/3.00  --bc_imp_inh                            [conj_cone]
% 19.19/3.00  --conj_cone_tolerance                   3.
% 19.19/3.00  --extra_neg_conj                        none
% 19.19/3.00  --large_theory_mode                     true
% 19.19/3.00  --prolific_symb_bound                   200
% 19.19/3.00  --lt_threshold                          2000
% 19.19/3.00  --clause_weak_htbl                      true
% 19.19/3.00  --gc_record_bc_elim                     false
% 19.19/3.00  
% 19.19/3.00  ------ Preprocessing Options
% 19.19/3.00  
% 19.19/3.00  --preprocessing_flag                    true
% 19.19/3.00  --time_out_prep_mult                    0.1
% 19.19/3.00  --splitting_mode                        input
% 19.19/3.00  --splitting_grd                         true
% 19.19/3.00  --splitting_cvd                         false
% 19.19/3.00  --splitting_cvd_svl                     false
% 19.19/3.00  --splitting_nvd                         32
% 19.19/3.00  --sub_typing                            true
% 19.19/3.00  --prep_gs_sim                           true
% 19.19/3.00  --prep_unflatten                        true
% 19.19/3.00  --prep_res_sim                          true
% 19.19/3.00  --prep_upred                            true
% 19.19/3.00  --prep_sem_filter                       exhaustive
% 19.19/3.00  --prep_sem_filter_out                   false
% 19.19/3.00  --pred_elim                             true
% 19.19/3.00  --res_sim_input                         true
% 19.19/3.00  --eq_ax_congr_red                       true
% 19.19/3.00  --pure_diseq_elim                       true
% 19.19/3.00  --brand_transform                       false
% 19.19/3.00  --non_eq_to_eq                          false
% 19.19/3.00  --prep_def_merge                        true
% 19.19/3.00  --prep_def_merge_prop_impl              false
% 19.19/3.00  --prep_def_merge_mbd                    true
% 19.19/3.00  --prep_def_merge_tr_red                 false
% 19.19/3.00  --prep_def_merge_tr_cl                  false
% 19.19/3.00  --smt_preprocessing                     true
% 19.19/3.00  --smt_ac_axioms                         fast
% 19.19/3.00  --preprocessed_out                      false
% 19.19/3.00  --preprocessed_stats                    false
% 19.19/3.00  
% 19.19/3.00  ------ Abstraction refinement Options
% 19.19/3.00  
% 19.19/3.00  --abstr_ref                             []
% 19.19/3.00  --abstr_ref_prep                        false
% 19.19/3.00  --abstr_ref_until_sat                   false
% 19.19/3.00  --abstr_ref_sig_restrict                funpre
% 19.19/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.19/3.00  --abstr_ref_under                       []
% 19.19/3.00  
% 19.19/3.00  ------ SAT Options
% 19.19/3.00  
% 19.19/3.00  --sat_mode                              false
% 19.19/3.00  --sat_fm_restart_options                ""
% 19.19/3.00  --sat_gr_def                            false
% 19.19/3.00  --sat_epr_types                         true
% 19.19/3.00  --sat_non_cyclic_types                  false
% 19.19/3.00  --sat_finite_models                     false
% 19.19/3.00  --sat_fm_lemmas                         false
% 19.19/3.00  --sat_fm_prep                           false
% 19.19/3.00  --sat_fm_uc_incr                        true
% 19.19/3.00  --sat_out_model                         small
% 19.19/3.00  --sat_out_clauses                       false
% 19.19/3.00  
% 19.19/3.00  ------ QBF Options
% 19.19/3.00  
% 19.19/3.00  --qbf_mode                              false
% 19.19/3.00  --qbf_elim_univ                         false
% 19.19/3.00  --qbf_dom_inst                          none
% 19.19/3.00  --qbf_dom_pre_inst                      false
% 19.19/3.00  --qbf_sk_in                             false
% 19.19/3.00  --qbf_pred_elim                         true
% 19.19/3.00  --qbf_split                             512
% 19.19/3.00  
% 19.19/3.00  ------ BMC1 Options
% 19.19/3.00  
% 19.19/3.00  --bmc1_incremental                      false
% 19.19/3.00  --bmc1_axioms                           reachable_all
% 19.19/3.00  --bmc1_min_bound                        0
% 19.19/3.00  --bmc1_max_bound                        -1
% 19.19/3.00  --bmc1_max_bound_default                -1
% 19.19/3.00  --bmc1_symbol_reachability              true
% 19.19/3.00  --bmc1_property_lemmas                  false
% 19.19/3.00  --bmc1_k_induction                      false
% 19.19/3.00  --bmc1_non_equiv_states                 false
% 19.19/3.00  --bmc1_deadlock                         false
% 19.19/3.00  --bmc1_ucm                              false
% 19.19/3.00  --bmc1_add_unsat_core                   none
% 19.19/3.00  --bmc1_unsat_core_children              false
% 19.19/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.19/3.00  --bmc1_out_stat                         full
% 19.19/3.00  --bmc1_ground_init                      false
% 19.19/3.00  --bmc1_pre_inst_next_state              false
% 19.19/3.00  --bmc1_pre_inst_state                   false
% 19.19/3.00  --bmc1_pre_inst_reach_state             false
% 19.19/3.00  --bmc1_out_unsat_core                   false
% 19.19/3.00  --bmc1_aig_witness_out                  false
% 19.19/3.00  --bmc1_verbose                          false
% 19.19/3.00  --bmc1_dump_clauses_tptp                false
% 19.19/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.19/3.00  --bmc1_dump_file                        -
% 19.19/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.19/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.19/3.00  --bmc1_ucm_extend_mode                  1
% 19.19/3.00  --bmc1_ucm_init_mode                    2
% 19.19/3.00  --bmc1_ucm_cone_mode                    none
% 19.19/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.19/3.00  --bmc1_ucm_relax_model                  4
% 19.19/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.19/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.19/3.00  --bmc1_ucm_layered_model                none
% 19.19/3.00  --bmc1_ucm_max_lemma_size               10
% 19.19/3.00  
% 19.19/3.00  ------ AIG Options
% 19.19/3.00  
% 19.19/3.00  --aig_mode                              false
% 19.19/3.00  
% 19.19/3.00  ------ Instantiation Options
% 19.19/3.00  
% 19.19/3.00  --instantiation_flag                    true
% 19.19/3.00  --inst_sos_flag                         true
% 19.19/3.00  --inst_sos_phase                        true
% 19.19/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.19/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.19/3.00  --inst_lit_sel_side                     num_symb
% 19.19/3.00  --inst_solver_per_active                1400
% 19.19/3.00  --inst_solver_calls_frac                1.
% 19.19/3.00  --inst_passive_queue_type               priority_queues
% 19.19/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.19/3.00  --inst_passive_queues_freq              [25;2]
% 19.19/3.00  --inst_dismatching                      true
% 19.19/3.00  --inst_eager_unprocessed_to_passive     true
% 19.19/3.00  --inst_prop_sim_given                   true
% 19.19/3.00  --inst_prop_sim_new                     false
% 19.19/3.00  --inst_subs_new                         false
% 19.19/3.00  --inst_eq_res_simp                      false
% 19.19/3.00  --inst_subs_given                       false
% 19.19/3.00  --inst_orphan_elimination               true
% 19.19/3.00  --inst_learning_loop_flag               true
% 19.19/3.00  --inst_learning_start                   3000
% 19.19/3.00  --inst_learning_factor                  2
% 19.19/3.00  --inst_start_prop_sim_after_learn       3
% 19.19/3.00  --inst_sel_renew                        solver
% 19.19/3.00  --inst_lit_activity_flag                true
% 19.19/3.00  --inst_restr_to_given                   false
% 19.19/3.00  --inst_activity_threshold               500
% 19.19/3.00  --inst_out_proof                        true
% 19.19/3.00  
% 19.19/3.00  ------ Resolution Options
% 19.19/3.00  
% 19.19/3.00  --resolution_flag                       true
% 19.19/3.00  --res_lit_sel                           adaptive
% 19.19/3.00  --res_lit_sel_side                      none
% 19.19/3.00  --res_ordering                          kbo
% 19.19/3.00  --res_to_prop_solver                    active
% 19.19/3.00  --res_prop_simpl_new                    false
% 19.19/3.00  --res_prop_simpl_given                  true
% 19.19/3.00  --res_passive_queue_type                priority_queues
% 19.19/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.19/3.00  --res_passive_queues_freq               [15;5]
% 19.19/3.00  --res_forward_subs                      full
% 19.19/3.00  --res_backward_subs                     full
% 19.19/3.00  --res_forward_subs_resolution           true
% 19.19/3.00  --res_backward_subs_resolution          true
% 19.19/3.00  --res_orphan_elimination                true
% 19.19/3.00  --res_time_limit                        2.
% 19.19/3.00  --res_out_proof                         true
% 19.19/3.00  
% 19.19/3.00  ------ Superposition Options
% 19.19/3.00  
% 19.19/3.00  --superposition_flag                    true
% 19.19/3.00  --sup_passive_queue_type                priority_queues
% 19.19/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.19/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.19/3.00  --demod_completeness_check              fast
% 19.19/3.00  --demod_use_ground                      true
% 19.19/3.00  --sup_to_prop_solver                    passive
% 19.19/3.00  --sup_prop_simpl_new                    true
% 19.19/3.00  --sup_prop_simpl_given                  true
% 19.19/3.00  --sup_fun_splitting                     true
% 19.19/3.00  --sup_smt_interval                      50000
% 19.19/3.00  
% 19.19/3.00  ------ Superposition Simplification Setup
% 19.19/3.00  
% 19.19/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.19/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.19/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.19/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.19/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.19/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.19/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.19/3.00  --sup_immed_triv                        [TrivRules]
% 19.19/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/3.00  --sup_immed_bw_main                     []
% 19.19/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.19/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.19/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/3.00  --sup_input_bw                          []
% 19.19/3.00  
% 19.19/3.00  ------ Combination Options
% 19.19/3.00  
% 19.19/3.00  --comb_res_mult                         3
% 19.19/3.00  --comb_sup_mult                         2
% 19.19/3.00  --comb_inst_mult                        10
% 19.19/3.00  
% 19.19/3.00  ------ Debug Options
% 19.19/3.00  
% 19.19/3.00  --dbg_backtrace                         false
% 19.19/3.00  --dbg_dump_prop_clauses                 false
% 19.19/3.00  --dbg_dump_prop_clauses_file            -
% 19.19/3.00  --dbg_out_stat                          false
% 19.19/3.00  ------ Parsing...
% 19.19/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.19/3.00  
% 19.19/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.19/3.00  
% 19.19/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.19/3.00  
% 19.19/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.19/3.00  ------ Proving...
% 19.19/3.00  ------ Problem Properties 
% 19.19/3.00  
% 19.19/3.00  
% 19.19/3.00  clauses                                 39
% 19.19/3.00  conjectures                             5
% 19.19/3.00  EPR                                     11
% 19.19/3.00  Horn                                    30
% 19.19/3.00  unary                                   8
% 19.19/3.00  binary                                  11
% 19.19/3.00  lits                                    93
% 19.19/3.00  lits eq                                 12
% 19.19/3.00  fd_pure                                 0
% 19.19/3.00  fd_pseudo                               0
% 19.19/3.00  fd_cond                                 1
% 19.19/3.00  fd_pseudo_cond                          8
% 19.19/3.00  AC symbols                              0
% 19.19/3.00  
% 19.19/3.00  ------ Schedule dynamic 5 is on 
% 19.19/3.00  
% 19.19/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.19/3.00  
% 19.19/3.00  
% 19.19/3.00  ------ 
% 19.19/3.00  Current options:
% 19.19/3.00  ------ 
% 19.19/3.00  
% 19.19/3.00  ------ Input Options
% 19.19/3.00  
% 19.19/3.00  --out_options                           all
% 19.19/3.00  --tptp_safe_out                         true
% 19.19/3.00  --problem_path                          ""
% 19.19/3.00  --include_path                          ""
% 19.19/3.00  --clausifier                            res/vclausify_rel
% 19.19/3.00  --clausifier_options                    ""
% 19.19/3.00  --stdin                                 false
% 19.19/3.00  --stats_out                             all
% 19.19/3.00  
% 19.19/3.00  ------ General Options
% 19.19/3.00  
% 19.19/3.00  --fof                                   false
% 19.19/3.00  --time_out_real                         305.
% 19.19/3.00  --time_out_virtual                      -1.
% 19.19/3.00  --symbol_type_check                     false
% 19.19/3.00  --clausify_out                          false
% 19.19/3.00  --sig_cnt_out                           false
% 19.19/3.00  --trig_cnt_out                          false
% 19.19/3.00  --trig_cnt_out_tolerance                1.
% 19.19/3.00  --trig_cnt_out_sk_spl                   false
% 19.19/3.00  --abstr_cl_out                          false
% 19.19/3.00  
% 19.19/3.00  ------ Global Options
% 19.19/3.00  
% 19.19/3.00  --schedule                              default
% 19.19/3.00  --add_important_lit                     false
% 19.19/3.00  --prop_solver_per_cl                    1000
% 19.19/3.00  --min_unsat_core                        false
% 19.19/3.00  --soft_assumptions                      false
% 19.19/3.00  --soft_lemma_size                       3
% 19.19/3.00  --prop_impl_unit_size                   0
% 19.19/3.00  --prop_impl_unit                        []
% 19.19/3.00  --share_sel_clauses                     true
% 19.19/3.00  --reset_solvers                         false
% 19.19/3.00  --bc_imp_inh                            [conj_cone]
% 19.19/3.00  --conj_cone_tolerance                   3.
% 19.19/3.00  --extra_neg_conj                        none
% 19.19/3.00  --large_theory_mode                     true
% 19.19/3.00  --prolific_symb_bound                   200
% 19.19/3.00  --lt_threshold                          2000
% 19.19/3.00  --clause_weak_htbl                      true
% 19.19/3.00  --gc_record_bc_elim                     false
% 19.19/3.00  
% 19.19/3.00  ------ Preprocessing Options
% 19.19/3.00  
% 19.19/3.00  --preprocessing_flag                    true
% 19.19/3.00  --time_out_prep_mult                    0.1
% 19.19/3.00  --splitting_mode                        input
% 19.19/3.00  --splitting_grd                         true
% 19.19/3.00  --splitting_cvd                         false
% 19.19/3.00  --splitting_cvd_svl                     false
% 19.19/3.00  --splitting_nvd                         32
% 19.19/3.00  --sub_typing                            true
% 19.19/3.00  --prep_gs_sim                           true
% 19.19/3.00  --prep_unflatten                        true
% 19.19/3.00  --prep_res_sim                          true
% 19.19/3.00  --prep_upred                            true
% 19.19/3.00  --prep_sem_filter                       exhaustive
% 19.19/3.00  --prep_sem_filter_out                   false
% 19.19/3.00  --pred_elim                             true
% 19.19/3.00  --res_sim_input                         true
% 19.19/3.00  --eq_ax_congr_red                       true
% 19.19/3.00  --pure_diseq_elim                       true
% 19.19/3.00  --brand_transform                       false
% 19.19/3.00  --non_eq_to_eq                          false
% 19.19/3.00  --prep_def_merge                        true
% 19.19/3.00  --prep_def_merge_prop_impl              false
% 19.19/3.00  --prep_def_merge_mbd                    true
% 19.19/3.00  --prep_def_merge_tr_red                 false
% 19.19/3.00  --prep_def_merge_tr_cl                  false
% 19.19/3.00  --smt_preprocessing                     true
% 19.19/3.00  --smt_ac_axioms                         fast
% 19.19/3.00  --preprocessed_out                      false
% 19.19/3.00  --preprocessed_stats                    false
% 19.19/3.00  
% 19.19/3.00  ------ Abstraction refinement Options
% 19.19/3.00  
% 19.19/3.00  --abstr_ref                             []
% 19.19/3.00  --abstr_ref_prep                        false
% 19.19/3.00  --abstr_ref_until_sat                   false
% 19.19/3.00  --abstr_ref_sig_restrict                funpre
% 19.19/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.19/3.00  --abstr_ref_under                       []
% 19.19/3.00  
% 19.19/3.00  ------ SAT Options
% 19.19/3.00  
% 19.19/3.00  --sat_mode                              false
% 19.19/3.00  --sat_fm_restart_options                ""
% 19.19/3.00  --sat_gr_def                            false
% 19.19/3.00  --sat_epr_types                         true
% 19.19/3.00  --sat_non_cyclic_types                  false
% 19.19/3.00  --sat_finite_models                     false
% 19.19/3.00  --sat_fm_lemmas                         false
% 19.19/3.00  --sat_fm_prep                           false
% 19.19/3.00  --sat_fm_uc_incr                        true
% 19.19/3.00  --sat_out_model                         small
% 19.19/3.00  --sat_out_clauses                       false
% 19.19/3.00  
% 19.19/3.00  ------ QBF Options
% 19.19/3.00  
% 19.19/3.00  --qbf_mode                              false
% 19.19/3.00  --qbf_elim_univ                         false
% 19.19/3.00  --qbf_dom_inst                          none
% 19.19/3.00  --qbf_dom_pre_inst                      false
% 19.19/3.00  --qbf_sk_in                             false
% 19.19/3.00  --qbf_pred_elim                         true
% 19.19/3.00  --qbf_split                             512
% 19.19/3.00  
% 19.19/3.00  ------ BMC1 Options
% 19.19/3.00  
% 19.19/3.00  --bmc1_incremental                      false
% 19.19/3.00  --bmc1_axioms                           reachable_all
% 19.19/3.00  --bmc1_min_bound                        0
% 19.19/3.00  --bmc1_max_bound                        -1
% 19.19/3.00  --bmc1_max_bound_default                -1
% 19.19/3.00  --bmc1_symbol_reachability              true
% 19.19/3.00  --bmc1_property_lemmas                  false
% 19.19/3.00  --bmc1_k_induction                      false
% 19.19/3.00  --bmc1_non_equiv_states                 false
% 19.19/3.00  --bmc1_deadlock                         false
% 19.19/3.00  --bmc1_ucm                              false
% 19.19/3.00  --bmc1_add_unsat_core                   none
% 19.19/3.00  --bmc1_unsat_core_children              false
% 19.19/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.19/3.00  --bmc1_out_stat                         full
% 19.19/3.00  --bmc1_ground_init                      false
% 19.19/3.00  --bmc1_pre_inst_next_state              false
% 19.19/3.00  --bmc1_pre_inst_state                   false
% 19.19/3.00  --bmc1_pre_inst_reach_state             false
% 19.19/3.00  --bmc1_out_unsat_core                   false
% 19.19/3.00  --bmc1_aig_witness_out                  false
% 19.19/3.00  --bmc1_verbose                          false
% 19.19/3.00  --bmc1_dump_clauses_tptp                false
% 19.19/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.19/3.00  --bmc1_dump_file                        -
% 19.19/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.19/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.19/3.00  --bmc1_ucm_extend_mode                  1
% 19.19/3.00  --bmc1_ucm_init_mode                    2
% 19.19/3.00  --bmc1_ucm_cone_mode                    none
% 19.19/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.19/3.00  --bmc1_ucm_relax_model                  4
% 19.19/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.19/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.19/3.00  --bmc1_ucm_layered_model                none
% 19.19/3.00  --bmc1_ucm_max_lemma_size               10
% 19.19/3.00  
% 19.19/3.00  ------ AIG Options
% 19.19/3.00  
% 19.19/3.00  --aig_mode                              false
% 19.19/3.00  
% 19.19/3.00  ------ Instantiation Options
% 19.19/3.00  
% 19.19/3.00  --instantiation_flag                    true
% 19.19/3.00  --inst_sos_flag                         true
% 19.19/3.00  --inst_sos_phase                        true
% 19.19/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.19/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.19/3.00  --inst_lit_sel_side                     none
% 19.19/3.00  --inst_solver_per_active                1400
% 19.19/3.00  --inst_solver_calls_frac                1.
% 19.19/3.00  --inst_passive_queue_type               priority_queues
% 19.19/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.19/3.00  --inst_passive_queues_freq              [25;2]
% 19.19/3.00  --inst_dismatching                      true
% 19.19/3.00  --inst_eager_unprocessed_to_passive     true
% 19.19/3.00  --inst_prop_sim_given                   true
% 19.19/3.00  --inst_prop_sim_new                     false
% 19.19/3.00  --inst_subs_new                         false
% 19.19/3.00  --inst_eq_res_simp                      false
% 19.19/3.00  --inst_subs_given                       false
% 19.19/3.00  --inst_orphan_elimination               true
% 19.19/3.00  --inst_learning_loop_flag               true
% 19.19/3.00  --inst_learning_start                   3000
% 19.19/3.00  --inst_learning_factor                  2
% 19.19/3.00  --inst_start_prop_sim_after_learn       3
% 19.19/3.00  --inst_sel_renew                        solver
% 19.19/3.00  --inst_lit_activity_flag                true
% 19.19/3.00  --inst_restr_to_given                   false
% 19.19/3.00  --inst_activity_threshold               500
% 19.19/3.00  --inst_out_proof                        true
% 19.19/3.00  
% 19.19/3.00  ------ Resolution Options
% 19.19/3.00  
% 19.19/3.00  --resolution_flag                       false
% 19.19/3.00  --res_lit_sel                           adaptive
% 19.19/3.00  --res_lit_sel_side                      none
% 19.19/3.00  --res_ordering                          kbo
% 19.19/3.00  --res_to_prop_solver                    active
% 19.19/3.00  --res_prop_simpl_new                    false
% 19.19/3.00  --res_prop_simpl_given                  true
% 19.19/3.00  --res_passive_queue_type                priority_queues
% 19.19/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.19/3.00  --res_passive_queues_freq               [15;5]
% 19.19/3.00  --res_forward_subs                      full
% 19.19/3.00  --res_backward_subs                     full
% 19.19/3.00  --res_forward_subs_resolution           true
% 19.19/3.00  --res_backward_subs_resolution          true
% 19.19/3.00  --res_orphan_elimination                true
% 19.19/3.00  --res_time_limit                        2.
% 19.19/3.00  --res_out_proof                         true
% 19.19/3.00  
% 19.19/3.00  ------ Superposition Options
% 19.19/3.00  
% 19.19/3.00  --superposition_flag                    true
% 19.19/3.00  --sup_passive_queue_type                priority_queues
% 19.19/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.19/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.19/3.00  --demod_completeness_check              fast
% 19.19/3.00  --demod_use_ground                      true
% 19.19/3.00  --sup_to_prop_solver                    passive
% 19.19/3.00  --sup_prop_simpl_new                    true
% 19.19/3.00  --sup_prop_simpl_given                  true
% 19.19/3.00  --sup_fun_splitting                     true
% 19.19/3.00  --sup_smt_interval                      50000
% 19.19/3.00  
% 19.19/3.00  ------ Superposition Simplification Setup
% 19.19/3.00  
% 19.19/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.19/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.19/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.19/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.19/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.19/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.19/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.19/3.00  --sup_immed_triv                        [TrivRules]
% 19.19/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/3.00  --sup_immed_bw_main                     []
% 19.19/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.19/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.19/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/3.00  --sup_input_bw                          []
% 19.19/3.00  
% 19.19/3.00  ------ Combination Options
% 19.19/3.00  
% 19.19/3.00  --comb_res_mult                         3
% 19.19/3.00  --comb_sup_mult                         2
% 19.19/3.00  --comb_inst_mult                        10
% 19.19/3.00  
% 19.19/3.00  ------ Debug Options
% 19.19/3.00  
% 19.19/3.00  --dbg_backtrace                         false
% 19.19/3.00  --dbg_dump_prop_clauses                 false
% 19.19/3.00  --dbg_dump_prop_clauses_file            -
% 19.19/3.00  --dbg_out_stat                          false
% 19.19/3.00  
% 19.19/3.00  
% 19.19/3.00  
% 19.19/3.00  
% 19.19/3.00  ------ Proving...
% 19.19/3.00  
% 19.19/3.00  
% 19.19/3.00  % SZS status Theorem for theBenchmark.p
% 19.19/3.00  
% 19.19/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.19/3.00  
% 19.19/3.00  fof(f1,axiom,(
% 19.19/3.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.19/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/3.00  
% 19.19/3.00  fof(f21,plain,(
% 19.19/3.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.19/3.00    inference(ennf_transformation,[],[f1])).
% 19.19/3.00  
% 19.19/3.00  fof(f33,plain,(
% 19.19/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.19/3.00    inference(nnf_transformation,[],[f21])).
% 19.19/3.00  
% 19.19/3.00  fof(f34,plain,(
% 19.19/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.19/3.00    inference(rectify,[],[f33])).
% 19.19/3.00  
% 19.19/3.00  fof(f35,plain,(
% 19.19/3.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.19/3.00    introduced(choice_axiom,[])).
% 19.19/3.00  
% 19.19/3.00  fof(f36,plain,(
% 19.19/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.19/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 19.19/3.00  
% 19.19/3.00  fof(f61,plain,(
% 19.19/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f36])).
% 19.19/3.00  
% 19.19/3.00  fof(f62,plain,(
% 19.19/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f36])).
% 19.19/3.00  
% 19.19/3.00  fof(f16,axiom,(
% 19.19/3.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 19.19/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/3.00  
% 19.19/3.00  fof(f28,plain,(
% 19.19/3.00    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.19/3.00    inference(ennf_transformation,[],[f16])).
% 19.19/3.00  
% 19.19/3.00  fof(f53,plain,(
% 19.19/3.00    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.19/3.00    inference(nnf_transformation,[],[f28])).
% 19.19/3.00  
% 19.19/3.00  fof(f94,plain,(
% 19.19/3.00    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.19/3.00    inference(cnf_transformation,[],[f53])).
% 19.19/3.00  
% 19.19/3.00  fof(f2,axiom,(
% 19.19/3.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.19/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/3.00  
% 19.19/3.00  fof(f20,plain,(
% 19.19/3.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.19/3.00    inference(rectify,[],[f2])).
% 19.19/3.00  
% 19.19/3.00  fof(f22,plain,(
% 19.19/3.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.19/3.00    inference(ennf_transformation,[],[f20])).
% 19.19/3.00  
% 19.19/3.00  fof(f37,plain,(
% 19.19/3.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 19.19/3.00    introduced(choice_axiom,[])).
% 19.19/3.00  
% 19.19/3.00  fof(f38,plain,(
% 19.19/3.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.19/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f37])).
% 19.19/3.00  
% 19.19/3.00  fof(f64,plain,(
% 19.19/3.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f38])).
% 19.19/3.00  
% 19.19/3.00  fof(f63,plain,(
% 19.19/3.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f38])).
% 19.19/3.00  
% 19.19/3.00  fof(f8,axiom,(
% 19.19/3.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 19.19/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/3.00  
% 19.19/3.00  fof(f24,plain,(
% 19.19/3.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 19.19/3.00    inference(ennf_transformation,[],[f8])).
% 19.19/3.00  
% 19.19/3.00  fof(f51,plain,(
% 19.19/3.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 19.19/3.00    inference(nnf_transformation,[],[f24])).
% 19.19/3.00  
% 19.19/3.00  fof(f84,plain,(
% 19.19/3.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f51])).
% 19.19/3.00  
% 19.19/3.00  fof(f18,conjecture,(
% 19.19/3.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (~r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 19.19/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/3.00  
% 19.19/3.00  fof(f19,negated_conjecture,(
% 19.19/3.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (~r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 19.19/3.00    inference(negated_conjecture,[],[f18])).
% 19.19/3.00  
% 19.19/3.00  fof(f31,plain,(
% 19.19/3.00    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((~r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.19/3.00    inference(ennf_transformation,[],[f19])).
% 19.19/3.00  
% 19.19/3.00  fof(f32,plain,(
% 19.19/3.00    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((~r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.19/3.00    inference(flattening,[],[f31])).
% 19.19/3.00  
% 19.19/3.00  fof(f56,plain,(
% 19.19/3.00    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.19/3.00    inference(nnf_transformation,[],[f32])).
% 19.19/3.00  
% 19.19/3.00  fof(f58,plain,(
% 19.19/3.00    ( ! [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k3_subset_1(X0,sK9) != X1 & ! [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,sK9)) & (r2_hidden(X3,sK9) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(sK9,k1_zfmisc_1(X0)))) )),
% 19.19/3.00    introduced(choice_axiom,[])).
% 19.19/3.00  
% 19.19/3.00  fof(f57,plain,(
% 19.19/3.00    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k3_subset_1(sK7,X2) != sK8 & ! [X3] : (((~r2_hidden(X3,sK8) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | r2_hidden(X3,sK8))) | ~m1_subset_1(X3,sK7)) & m1_subset_1(X2,k1_zfmisc_1(sK7))) & m1_subset_1(sK8,k1_zfmisc_1(sK7)))),
% 19.19/3.00    introduced(choice_axiom,[])).
% 19.19/3.00  
% 19.19/3.00  fof(f59,plain,(
% 19.19/3.00    (k3_subset_1(sK7,sK9) != sK8 & ! [X3] : (((~r2_hidden(X3,sK8) | ~r2_hidden(X3,sK9)) & (r2_hidden(X3,sK9) | r2_hidden(X3,sK8))) | ~m1_subset_1(X3,sK7)) & m1_subset_1(sK9,k1_zfmisc_1(sK7))) & m1_subset_1(sK8,k1_zfmisc_1(sK7))),
% 19.19/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f56,f58,f57])).
% 19.19/3.00  
% 19.19/3.00  fof(f100,plain,(
% 19.19/3.00    ( ! [X3] : (~r2_hidden(X3,sK8) | ~r2_hidden(X3,sK9) | ~m1_subset_1(X3,sK7)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f59])).
% 19.19/3.00  
% 19.19/3.00  fof(f97,plain,(
% 19.19/3.00    m1_subset_1(sK8,k1_zfmisc_1(sK7))),
% 19.19/3.00    inference(cnf_transformation,[],[f59])).
% 19.19/3.00  
% 19.19/3.00  fof(f82,plain,(
% 19.19/3.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f51])).
% 19.19/3.00  
% 19.19/3.00  fof(f4,axiom,(
% 19.19/3.00    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 19.19/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/3.00  
% 19.19/3.00  fof(f23,plain,(
% 19.19/3.00    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 19.19/3.00    inference(ennf_transformation,[],[f4])).
% 19.19/3.00  
% 19.19/3.00  fof(f69,plain,(
% 19.19/3.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f23])).
% 19.19/3.00  
% 19.19/3.00  fof(f13,axiom,(
% 19.19/3.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 19.19/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/3.00  
% 19.19/3.00  fof(f26,plain,(
% 19.19/3.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.19/3.00    inference(ennf_transformation,[],[f13])).
% 19.19/3.00  
% 19.19/3.00  fof(f89,plain,(
% 19.19/3.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.19/3.00    inference(cnf_transformation,[],[f26])).
% 19.19/3.00  
% 19.19/3.00  fof(f65,plain,(
% 19.19/3.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f38])).
% 19.19/3.00  
% 19.19/3.00  fof(f99,plain,(
% 19.19/3.00    ( ! [X3] : (r2_hidden(X3,sK9) | r2_hidden(X3,sK8) | ~m1_subset_1(X3,sK7)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f59])).
% 19.19/3.00  
% 19.19/3.00  fof(f12,axiom,(
% 19.19/3.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 19.19/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/3.00  
% 19.19/3.00  fof(f25,plain,(
% 19.19/3.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.19/3.00    inference(ennf_transformation,[],[f12])).
% 19.19/3.00  
% 19.19/3.00  fof(f88,plain,(
% 19.19/3.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.19/3.00    inference(cnf_transformation,[],[f25])).
% 19.19/3.00  
% 19.19/3.00  fof(f3,axiom,(
% 19.19/3.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.19/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/3.00  
% 19.19/3.00  fof(f39,plain,(
% 19.19/3.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.19/3.00    inference(nnf_transformation,[],[f3])).
% 19.19/3.00  
% 19.19/3.00  fof(f40,plain,(
% 19.19/3.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.19/3.00    inference(flattening,[],[f39])).
% 19.19/3.00  
% 19.19/3.00  fof(f68,plain,(
% 19.19/3.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.19/3.00    inference(cnf_transformation,[],[f40])).
% 19.19/3.00  
% 19.19/3.00  fof(f93,plain,(
% 19.19/3.00    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.19/3.00    inference(cnf_transformation,[],[f53])).
% 19.19/3.00  
% 19.19/3.00  fof(f101,plain,(
% 19.19/3.00    k3_subset_1(sK7,sK9) != sK8),
% 19.19/3.00    inference(cnf_transformation,[],[f59])).
% 19.19/3.00  
% 19.19/3.00  fof(f98,plain,(
% 19.19/3.00    m1_subset_1(sK9,k1_zfmisc_1(sK7))),
% 19.19/3.00    inference(cnf_transformation,[],[f59])).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1,plain,
% 19.19/3.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f61]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_78272,plain,
% 19.19/3.00      ( r2_hidden(sK0(k3_subset_1(sK7,sK9),X0),k3_subset_1(sK7,sK9))
% 19.19/3.00      | r1_tarski(k3_subset_1(sK7,sK9),X0) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_1]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_80115,plain,
% 19.19/3.00      ( r2_hidden(sK0(k3_subset_1(sK7,sK9),k3_subset_1(sK7,sK9)),k3_subset_1(sK7,sK9))
% 19.19/3.00      | r1_tarski(k3_subset_1(sK7,sK9),k3_subset_1(sK7,sK9)) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_78272]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_0,plain,
% 19.19/3.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f62]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_78271,plain,
% 19.19/3.00      ( ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),X0),X0)
% 19.19/3.00      | r1_tarski(k3_subset_1(sK7,sK9),X0) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_0]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_80114,plain,
% 19.19/3.00      ( ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),k3_subset_1(sK7,sK9)),k3_subset_1(sK7,sK9))
% 19.19/3.00      | r1_tarski(k3_subset_1(sK7,sK9),k3_subset_1(sK7,sK9)) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_78271]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_31,plain,
% 19.19/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.19/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.19/3.00      | r1_xboole_0(X0,X2)
% 19.19/3.00      | ~ r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 19.19/3.00      inference(cnf_transformation,[],[f94]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_12186,plain,
% 19.19/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.19/3.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(X1))
% 19.19/3.00      | r1_xboole_0(X0,sK9)
% 19.19/3.00      | ~ r1_tarski(X0,k3_subset_1(X1,sK9)) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_31]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_33996,plain,
% 19.19/3.00      ( ~ m1_subset_1(k3_subset_1(sK7,sK9),k1_zfmisc_1(X0))
% 19.19/3.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(X0))
% 19.19/3.00      | r1_xboole_0(k3_subset_1(sK7,sK9),sK9)
% 19.19/3.00      | ~ r1_tarski(k3_subset_1(sK7,sK9),k3_subset_1(X0,sK9)) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_12186]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_64992,plain,
% 19.19/3.00      ( ~ m1_subset_1(k3_subset_1(sK7,sK9),k1_zfmisc_1(sK7))
% 19.19/3.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(sK7))
% 19.19/3.00      | r1_xboole_0(k3_subset_1(sK7,sK9),sK9)
% 19.19/3.00      | ~ r1_tarski(k3_subset_1(sK7,sK9),k3_subset_1(sK7,sK9)) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_33996]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4,plain,
% 19.19/3.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f64]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1797,plain,
% 19.19/3.00      ( r1_xboole_0(X0,X1) = iProver_top
% 19.19/3.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5,plain,
% 19.19/3.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 19.19/3.00      inference(cnf_transformation,[],[f63]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1796,plain,
% 19.19/3.00      ( r1_xboole_0(X0,X1) = iProver_top
% 19.19/3.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_21,plain,
% 19.19/3.00      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f84]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1782,plain,
% 19.19/3.00      ( m1_subset_1(X0,X1) = iProver_top
% 19.19/3.00      | v1_xboole_0(X1) != iProver_top
% 19.19/3.00      | v1_xboole_0(X0) != iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_36,negated_conjecture,
% 19.19/3.00      ( ~ m1_subset_1(X0,sK7)
% 19.19/3.00      | ~ r2_hidden(X0,sK8)
% 19.19/3.00      | ~ r2_hidden(X0,sK9) ),
% 19.19/3.00      inference(cnf_transformation,[],[f100]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1771,plain,
% 19.19/3.00      ( m1_subset_1(X0,sK7) != iProver_top
% 19.19/3.00      | r2_hidden(X0,sK8) != iProver_top
% 19.19/3.00      | r2_hidden(X0,sK9) != iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4931,plain,
% 19.19/3.00      ( r2_hidden(X0,sK8) != iProver_top
% 19.19/3.00      | r2_hidden(X0,sK9) != iProver_top
% 19.19/3.00      | v1_xboole_0(X0) != iProver_top
% 19.19/3.00      | v1_xboole_0(sK7) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_1782,c_1771]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_39,negated_conjecture,
% 19.19/3.00      ( m1_subset_1(sK8,k1_zfmisc_1(sK7)) ),
% 19.19/3.00      inference(cnf_transformation,[],[f97]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_40,plain,
% 19.19/3.00      ( m1_subset_1(sK8,k1_zfmisc_1(sK7)) = iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_45,plain,
% 19.19/3.00      ( m1_subset_1(X0,sK7) != iProver_top
% 19.19/3.00      | r2_hidden(X0,sK8) != iProver_top
% 19.19/3.00      | r2_hidden(X0,sK9) != iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_23,plain,
% 19.19/3.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f82]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_9,plain,
% 19.19/3.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f69]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_230,plain,
% 19.19/3.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 19.19/3.00      inference(global_propositional_subsumption,
% 19.19/3.00                [status(thm)],
% 19.19/3.00                [c_23,c_9]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_231,plain,
% 19.19/3.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 19.19/3.00      inference(renaming,[status(thm)],[c_230]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1855,plain,
% 19.19/3.00      ( m1_subset_1(X0,sK7) | ~ r2_hidden(X0,sK7) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_231]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1856,plain,
% 19.19/3.00      ( m1_subset_1(X0,sK7) = iProver_top
% 19.19/3.00      | r2_hidden(X0,sK7) != iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_1855]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_28,plain,
% 19.19/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.19/3.00      | ~ r2_hidden(X2,X0)
% 19.19/3.00      | r2_hidden(X2,X1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f89]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1929,plain,
% 19.19/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
% 19.19/3.00      | ~ r2_hidden(X1,X0)
% 19.19/3.00      | r2_hidden(X1,sK7) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_28]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2293,plain,
% 19.19/3.00      ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK7))
% 19.19/3.00      | ~ r2_hidden(X0,sK8)
% 19.19/3.00      | r2_hidden(X0,sK7) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_1929]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2294,plain,
% 19.19/3.00      ( m1_subset_1(sK8,k1_zfmisc_1(sK7)) != iProver_top
% 19.19/3.00      | r2_hidden(X0,sK8) != iProver_top
% 19.19/3.00      | r2_hidden(X0,sK7) = iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_2293]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5573,plain,
% 19.19/3.00      ( r2_hidden(X0,sK8) != iProver_top
% 19.19/3.00      | r2_hidden(X0,sK9) != iProver_top ),
% 19.19/3.00      inference(global_propositional_subsumption,
% 19.19/3.00                [status(thm)],
% 19.19/3.00                [c_4931,c_40,c_45,c_1856,c_2294]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5581,plain,
% 19.19/3.00      ( r1_xboole_0(sK8,X0) = iProver_top
% 19.19/3.00      | r2_hidden(sK1(sK8,X0),sK9) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_1796,c_5573]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5940,plain,
% 19.19/3.00      ( r1_xboole_0(sK8,sK9) = iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_1797,c_5581]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5941,plain,
% 19.19/3.00      ( r1_xboole_0(sK8,sK9) ),
% 19.19/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_5940]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_3,plain,
% 19.19/3.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 19.19/3.00      inference(cnf_transformation,[],[f65]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2210,plain,
% 19.19/3.00      ( ~ r1_xboole_0(k3_subset_1(sK7,sK9),X0)
% 19.19/3.00      | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),X0)
% 19.19/3.00      | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),k3_subset_1(sK7,sK9)) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_3]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5757,plain,
% 19.19/3.00      ( ~ r1_xboole_0(k3_subset_1(sK7,sK9),sK9)
% 19.19/3.00      | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),k3_subset_1(sK7,sK9))
% 19.19/3.00      | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK9) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_2210]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_37,negated_conjecture,
% 19.19/3.00      ( ~ m1_subset_1(X0,sK7) | r2_hidden(X0,sK8) | r2_hidden(X0,sK9) ),
% 19.19/3.00      inference(cnf_transformation,[],[f99]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5755,plain,
% 19.19/3.00      ( ~ m1_subset_1(sK0(k3_subset_1(sK7,sK9),sK8),sK7)
% 19.19/3.00      | r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK8)
% 19.19/3.00      | r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK9) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_37]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5710,plain,
% 19.19/3.00      ( m1_subset_1(sK0(k3_subset_1(sK7,sK9),sK8),sK7)
% 19.19/3.00      | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK7) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_1855]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_27,plain,
% 19.19/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.19/3.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 19.19/3.00      inference(cnf_transformation,[],[f88]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_3119,plain,
% 19.19/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
% 19.19/3.00      | m1_subset_1(k3_subset_1(sK7,X0),k1_zfmisc_1(sK7)) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_27]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5020,plain,
% 19.19/3.00      ( m1_subset_1(k3_subset_1(sK7,sK9),k1_zfmisc_1(sK7))
% 19.19/3.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(sK7)) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_3119]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2311,plain,
% 19.19/3.00      ( ~ m1_subset_1(k3_subset_1(sK7,X0),k1_zfmisc_1(sK7))
% 19.19/3.00      | ~ r2_hidden(X1,k3_subset_1(sK7,X0))
% 19.19/3.00      | r2_hidden(X1,sK7) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_1929]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4337,plain,
% 19.19/3.00      ( ~ m1_subset_1(k3_subset_1(sK7,sK9),k1_zfmisc_1(sK7))
% 19.19/3.00      | ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),k3_subset_1(sK7,sK9))
% 19.19/3.00      | r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK7) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_2311]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1049,plain,( X0 = X0 ),theory(equality) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_3085,plain,
% 19.19/3.00      ( k3_subset_1(sK7,sK9) = k3_subset_1(sK7,sK9) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_1049]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1050,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1852,plain,
% 19.19/3.00      ( k3_subset_1(sK7,sK9) != X0
% 19.19/3.00      | k3_subset_1(sK7,sK9) = sK8
% 19.19/3.00      | sK8 != X0 ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_1050]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2611,plain,
% 19.19/3.00      ( k3_subset_1(sK7,sK9) != k3_subset_1(sK7,sK9)
% 19.19/3.00      | k3_subset_1(sK7,sK9) = sK8
% 19.19/3.00      | sK8 != k3_subset_1(sK7,sK9) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_1852]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_6,plain,
% 19.19/3.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 19.19/3.00      inference(cnf_transformation,[],[f68]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1916,plain,
% 19.19/3.00      ( ~ r1_tarski(X0,sK8) | ~ r1_tarski(sK8,X0) | sK8 = X0 ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_6]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2066,plain,
% 19.19/3.00      ( ~ r1_tarski(k3_subset_1(sK7,sK9),sK8)
% 19.19/3.00      | ~ r1_tarski(sK8,k3_subset_1(sK7,sK9))
% 19.19/3.00      | sK8 = k3_subset_1(sK7,sK9) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_1916]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_32,plain,
% 19.19/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.19/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.19/3.00      | ~ r1_xboole_0(X0,X2)
% 19.19/3.00      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 19.19/3.00      inference(cnf_transformation,[],[f93]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2024,plain,
% 19.19/3.00      ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK7))
% 19.19/3.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(sK7))
% 19.19/3.00      | ~ r1_xboole_0(sK8,sK9)
% 19.19/3.00      | r1_tarski(sK8,k3_subset_1(sK7,sK9)) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_32]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1892,plain,
% 19.19/3.00      ( ~ r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),sK8)
% 19.19/3.00      | r1_tarski(k3_subset_1(sK7,sK9),sK8) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_0]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_1893,plain,
% 19.19/3.00      ( r2_hidden(sK0(k3_subset_1(sK7,sK9),sK8),k3_subset_1(sK7,sK9))
% 19.19/3.00      | r1_tarski(k3_subset_1(sK7,sK9),sK8) ),
% 19.19/3.00      inference(instantiation,[status(thm)],[c_1]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_35,negated_conjecture,
% 19.19/3.00      ( k3_subset_1(sK7,sK9) != sK8 ),
% 19.19/3.00      inference(cnf_transformation,[],[f101]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_38,negated_conjecture,
% 19.19/3.00      ( m1_subset_1(sK9,k1_zfmisc_1(sK7)) ),
% 19.19/3.00      inference(cnf_transformation,[],[f98]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(contradiction,plain,
% 19.19/3.00      ( $false ),
% 19.19/3.00      inference(minisat,
% 19.19/3.00                [status(thm)],
% 19.19/3.00                [c_80115,c_80114,c_64992,c_5941,c_5757,c_5755,c_5710,
% 19.19/3.00                 c_5020,c_4337,c_3085,c_2611,c_2066,c_2024,c_1892,c_1893,
% 19.19/3.00                 c_35,c_38,c_39]) ).
% 19.19/3.00  
% 19.19/3.00  
% 19.19/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.19/3.00  
% 19.19/3.00  ------                               Statistics
% 19.19/3.00  
% 19.19/3.00  ------ General
% 19.19/3.00  
% 19.19/3.00  abstr_ref_over_cycles:                  0
% 19.19/3.00  abstr_ref_under_cycles:                 0
% 19.19/3.00  gc_basic_clause_elim:                   0
% 19.19/3.00  forced_gc_time:                         0
% 19.19/3.00  parsing_time:                           0.007
% 19.19/3.00  unif_index_cands_time:                  0.
% 19.19/3.00  unif_index_add_time:                    0.
% 19.19/3.00  orderings_time:                         0.
% 19.19/3.00  out_proof_time:                         0.011
% 19.19/3.00  total_time:                             2.009
% 19.19/3.00  num_of_symbols:                         50
% 19.19/3.00  num_of_terms:                           37253
% 19.19/3.00  
% 19.19/3.00  ------ Preprocessing
% 19.19/3.00  
% 19.19/3.00  num_of_splits:                          0
% 19.19/3.00  num_of_split_atoms:                     0
% 19.19/3.00  num_of_reused_defs:                     0
% 19.19/3.00  num_eq_ax_congr_red:                    51
% 19.19/3.00  num_of_sem_filtered_clauses:            1
% 19.19/3.00  num_of_subtypes:                        0
% 19.19/3.00  monotx_restored_types:                  0
% 19.19/3.00  sat_num_of_epr_types:                   0
% 19.19/3.00  sat_num_of_non_cyclic_types:            0
% 19.19/3.00  sat_guarded_non_collapsed_types:        0
% 19.19/3.00  num_pure_diseq_elim:                    0
% 19.19/3.00  simp_replaced_by:                       0
% 19.19/3.00  res_preprocessed:                       173
% 19.19/3.00  prep_upred:                             0
% 19.19/3.00  prep_unflattend:                        12
% 19.19/3.00  smt_new_axioms:                         0
% 19.19/3.00  pred_elim_cands:                        5
% 19.19/3.00  pred_elim:                              0
% 19.19/3.00  pred_elim_cl:                           0
% 19.19/3.00  pred_elim_cycles:                       2
% 19.19/3.00  merged_defs:                            8
% 19.19/3.00  merged_defs_ncl:                        0
% 19.19/3.00  bin_hyper_res:                          8
% 19.19/3.00  prep_cycles:                            4
% 19.19/3.00  pred_elim_time:                         0.016
% 19.19/3.00  splitting_time:                         0.
% 19.19/3.00  sem_filter_time:                        0.
% 19.19/3.00  monotx_time:                            0.
% 19.19/3.00  subtype_inf_time:                       0.
% 19.19/3.00  
% 19.19/3.00  ------ Problem properties
% 19.19/3.00  
% 19.19/3.00  clauses:                                39
% 19.19/3.00  conjectures:                            5
% 19.19/3.00  epr:                                    11
% 19.19/3.00  horn:                                   30
% 19.19/3.00  ground:                                 3
% 19.19/3.00  unary:                                  8
% 19.19/3.00  binary:                                 11
% 19.19/3.00  lits:                                   93
% 19.19/3.00  lits_eq:                                12
% 19.19/3.00  fd_pure:                                0
% 19.19/3.00  fd_pseudo:                              0
% 19.19/3.00  fd_cond:                                1
% 19.19/3.00  fd_pseudo_cond:                         8
% 19.19/3.00  ac_symbols:                             0
% 19.19/3.00  
% 19.19/3.00  ------ Propositional Solver
% 19.19/3.00  
% 19.19/3.00  prop_solver_calls:                      37
% 19.19/3.00  prop_fast_solver_calls:                 2878
% 19.19/3.00  smt_solver_calls:                       0
% 19.19/3.00  smt_fast_solver_calls:                  0
% 19.19/3.00  prop_num_of_clauses:                    31700
% 19.19/3.00  prop_preprocess_simplified:             46895
% 19.19/3.00  prop_fo_subsumed:                       127
% 19.19/3.00  prop_solver_time:                       0.
% 19.19/3.00  smt_solver_time:                        0.
% 19.19/3.00  smt_fast_solver_time:                   0.
% 19.19/3.00  prop_fast_solver_time:                  0.
% 19.19/3.00  prop_unsat_core_time:                   0.002
% 19.19/3.00  
% 19.19/3.00  ------ QBF
% 19.19/3.00  
% 19.19/3.00  qbf_q_res:                              0
% 19.19/3.00  qbf_num_tautologies:                    0
% 19.19/3.00  qbf_prep_cycles:                        0
% 19.19/3.00  
% 19.19/3.00  ------ BMC1
% 19.19/3.00  
% 19.19/3.00  bmc1_current_bound:                     -1
% 19.19/3.00  bmc1_last_solved_bound:                 -1
% 19.19/3.00  bmc1_unsat_core_size:                   -1
% 19.19/3.00  bmc1_unsat_core_parents_size:           -1
% 19.19/3.00  bmc1_merge_next_fun:                    0
% 19.19/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.19/3.00  
% 19.19/3.00  ------ Instantiation
% 19.19/3.00  
% 19.19/3.00  inst_num_of_clauses:                    202
% 19.19/3.00  inst_num_in_passive:                    36
% 19.19/3.00  inst_num_in_active:                     2362
% 19.19/3.00  inst_num_in_unprocessed:                90
% 19.19/3.00  inst_num_of_loops:                      3076
% 19.19/3.00  inst_num_of_learning_restarts:          1
% 19.19/3.00  inst_num_moves_active_passive:          713
% 19.19/3.00  inst_lit_activity:                      0
% 19.19/3.00  inst_lit_activity_moves:                0
% 19.19/3.00  inst_num_tautologies:                   0
% 19.19/3.00  inst_num_prop_implied:                  0
% 19.19/3.00  inst_num_existing_simplified:           0
% 19.19/3.00  inst_num_eq_res_simplified:             0
% 19.19/3.00  inst_num_child_elim:                    0
% 19.19/3.00  inst_num_of_dismatching_blockings:      10807
% 19.19/3.00  inst_num_of_non_proper_insts:           10665
% 19.19/3.00  inst_num_of_duplicates:                 0
% 19.19/3.00  inst_inst_num_from_inst_to_res:         0
% 19.19/3.00  inst_dismatching_checking_time:         0.
% 19.19/3.00  
% 19.19/3.00  ------ Resolution
% 19.19/3.00  
% 19.19/3.00  res_num_of_clauses:                     47
% 19.19/3.00  res_num_in_passive:                     47
% 19.19/3.00  res_num_in_active:                      0
% 19.19/3.00  res_num_of_loops:                       177
% 19.19/3.00  res_forward_subset_subsumed:            267
% 19.19/3.00  res_backward_subset_subsumed:           0
% 19.19/3.00  res_forward_subsumed:                   0
% 19.19/3.00  res_backward_subsumed:                  0
% 19.19/3.00  res_forward_subsumption_resolution:     0
% 19.19/3.00  res_backward_subsumption_resolution:    0
% 19.19/3.00  res_clause_to_clause_subsumption:       31607
% 19.19/3.00  res_orphan_elimination:                 0
% 19.19/3.00  res_tautology_del:                      1196
% 19.19/3.00  res_num_eq_res_simplified:              0
% 19.19/3.00  res_num_sel_changes:                    0
% 19.19/3.00  res_moves_from_active_to_pass:          0
% 19.19/3.00  
% 19.19/3.00  ------ Superposition
% 19.19/3.00  
% 19.19/3.00  sup_time_total:                         0.
% 19.19/3.00  sup_time_generating:                    0.
% 19.19/3.00  sup_time_sim_full:                      0.
% 19.19/3.00  sup_time_sim_immed:                     0.
% 19.19/3.00  
% 19.19/3.00  sup_num_of_clauses:                     4516
% 19.19/3.00  sup_num_in_active:                      582
% 19.19/3.00  sup_num_in_passive:                     3934
% 19.19/3.00  sup_num_of_loops:                       614
% 19.19/3.00  sup_fw_superposition:                   4906
% 19.19/3.00  sup_bw_superposition:                   3083
% 19.19/3.00  sup_immediate_simplified:               2329
% 19.19/3.00  sup_given_eliminated:                   3
% 19.19/3.00  comparisons_done:                       0
% 19.19/3.00  comparisons_avoided:                    0
% 19.19/3.00  
% 19.19/3.00  ------ Simplifications
% 19.19/3.00  
% 19.19/3.00  
% 19.19/3.00  sim_fw_subset_subsumed:                 1186
% 19.19/3.00  sim_bw_subset_subsumed:                 39
% 19.19/3.00  sim_fw_subsumed:                        912
% 19.19/3.00  sim_bw_subsumed:                        48
% 19.19/3.00  sim_fw_subsumption_res:                 0
% 19.19/3.00  sim_bw_subsumption_res:                 0
% 19.19/3.00  sim_tautology_del:                      67
% 19.19/3.00  sim_eq_tautology_del:                   66
% 19.19/3.00  sim_eq_res_simp:                        10
% 19.19/3.00  sim_fw_demodulated:                     163
% 19.19/3.00  sim_bw_demodulated:                     1
% 19.19/3.00  sim_light_normalised:                   59
% 19.19/3.00  sim_joinable_taut:                      0
% 19.19/3.00  sim_joinable_simp:                      0
% 19.19/3.00  sim_ac_normalised:                      0
% 19.19/3.00  sim_smt_subsumption:                    0
% 19.19/3.00  
%------------------------------------------------------------------------------
