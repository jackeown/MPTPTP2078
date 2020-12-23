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
% DateTime   : Thu Dec  3 12:13:58 EST 2020

% Result     : Theorem 11.25s
% Output     : CNFRefutation 11.25s
% Verified   : 
% Statistics : Number of formulae       :  270 (2049 expanded)
%              Number of clauses        :  146 ( 559 expanded)
%              Number of leaves         :   37 ( 491 expanded)
%              Depth                    :   27
%              Number of atoms          :  791 (14062 expanded)
%              Number of equality atoms :  252 ( 830 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f39])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f23,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f114,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f33,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,k1_tops_1(X0,X2))
            <=> ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f65])).

fof(f75,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f66])).

fof(f76,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f75])).

fof(f77,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f76])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK4)
        & r1_tarski(sK4,X2)
        & v3_pre_topc(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(sK2,X3)
              | ~ r1_tarski(X3,sK3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK2,k1_tops_1(X0,sK3)) )
        & ( ? [X4] :
              ( r2_hidden(sK2,X4)
              & r1_tarski(X4,sK3)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK2,k1_tops_1(X0,sK3)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X1,k1_tops_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X2,X1] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            | ~ r2_hidden(X1,k1_tops_1(sK1,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK1)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
            | r2_hidden(X1,k1_tops_1(sK1,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK2,X3)
          | ~ r1_tarski(X3,sK3)
          | ~ v3_pre_topc(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) )
    & ( ( r2_hidden(sK2,sK4)
        & r1_tarski(sK4,sK3)
        & v3_pre_topc(sK4,sK1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) )
      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f77,f80,f79,f78])).

fof(f126,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f117,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f116,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f86,f89])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f87,f89])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f128,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f81])).

fof(f127,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f81])).

fof(f132,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r1_tarski(X3,sK3)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f122,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f125,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f141,plain,(
    ! [X0] : r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f104,f95])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f103,f95])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f72])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f101,f95])).

fof(f144,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f137])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f67])).

fof(f69,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f68,f69])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f136,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) != k2_tarski(X0,X0) ) ),
    inference(definition_unfolding,[],[f96,f95,f95,f95])).

fof(f142,plain,(
    ! [X1] : k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) != k2_tarski(X1,X1) ),
    inference(equality_resolution,[],[f136])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f47])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v2_pre_topc(X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v2_pre_topc(X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f129,plain,
    ( v3_pre_topc(sK4,sK1)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f81])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f63])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f131,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f81])).

fof(f130,plain,
    ( r1_tarski(sK4,sK3)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1703,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,X3)
    | X2 = X1
    | k2_xboole_0(X2,X0) != k2_xboole_0(X3,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1701,plain,
    ( X0 = X1
    | k2_xboole_0(X0,X2) != k2_xboole_0(X3,X1)
    | r1_xboole_0(X2,X1) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6912,plain,
    ( X0 = X1
    | k2_xboole_0(X2,X0) != X1
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1701])).

cnf(c_7057,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_xboole_0(k2_xboole_0(X0,X1),X0) != iProver_top
    | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_6912])).

cnf(c_42190,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1703,c_7057])).

cnf(c_30,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1682,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_47,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_47])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_1675,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_33,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_32,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_506,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_33,c_32])).

cnf(c_566,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_506,c_47])).

cnf(c_567,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_1712,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1675,c_567])).

cnf(c_2628,plain,
    ( r1_tarski(k1_tops_1(sK1,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_1712])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1704,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4840,plain,
    ( k4_xboole_0(k1_tops_1(sK1,k1_xboole_0),k4_xboole_0(k1_tops_1(sK1,k1_xboole_0),k1_xboole_0)) = k1_tops_1(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2628,c_1704])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1709,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_6])).

cnf(c_4843,plain,
    ( k1_tops_1(sK1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4840,c_6,c_1709])).

cnf(c_5187,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4843,c_2628])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1700,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4583,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1700])).

cnf(c_7685,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5187,c_4583])).

cnf(c_42205,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_42190,c_7685])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1678,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_1711,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1678,c_567])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_1813,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_1814,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_41,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_38,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_48,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_520,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_48])).

cnf(c_521,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_47])).

cnf(c_526,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_525])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X0,sK3)
    | k1_tops_1(sK1,X1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_526])).

cnf(c_715,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_47])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_719,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_715,c_602])).

cnf(c_1833,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1834,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(c_2540,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1711,c_51,c_1814,c_1834])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1687,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5637,plain,
    ( k3_subset_1(k2_struct_0(sK1),sK4) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
    inference(superposition,[status(thm)],[c_2540,c_1687])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_47])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_1673,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_1714,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1673,c_567])).

cnf(c_2546,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
    inference(superposition,[status(thm)],[c_2540,c_1714])).

cnf(c_5856,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
    inference(demodulation,[status(thm)],[c_5637,c_2546])).

cnf(c_20,plain,
    ( r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_1692,plain,
    ( r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( r1_xboole_0(k2_tarski(X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_1693,plain,
    ( r1_xboole_0(k2_tarski(X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_1697,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1706,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1707,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5510,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1706,c_1707])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1702,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7720,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5510,c_1702])).

cnf(c_14961,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | r1_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_7720])).

cnf(c_13,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) != k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_1710,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13,c_1709])).

cnf(c_15216,plain,
    ( r1_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14961,c_1710])).

cnf(c_15217,plain,
    ( r1_xboole_0(k2_tarski(X0,X1),k2_tarski(X1,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15216])).

cnf(c_15222,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_15217])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1705,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15804,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_15222,c_1705])).

cnf(c_15979,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1692,c_15804])).

cnf(c_23,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1689,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15988,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15979,c_1689])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_101,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_18517,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15988,c_101])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1684,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_18525,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_18517,c_1684])).

cnf(c_18526,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_18517,c_1687])).

cnf(c_18593,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_18526,c_1709])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1683,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2898,plain,
    ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),X0),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_1683])).

cnf(c_18570,plain,
    ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_struct_0(sK1)),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) ),
    inference(superposition,[status(thm)],[c_18517,c_2898])).

cnf(c_18595,plain,
    ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) ),
    inference(demodulation,[status(thm)],[c_18593,c_18570])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1685,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3793,plain,
    ( k4_subset_1(k2_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_1685])).

cnf(c_4228,plain,
    ( k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) = k2_xboole_0(k1_xboole_0,sK4) ),
    inference(superposition,[status(thm)],[c_1682,c_3793])).

cnf(c_18599,plain,
    ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k2_xboole_0(k1_xboole_0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_18595,c_4228])).

cnf(c_18600,plain,
    ( k3_subset_1(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK4)) = k2_xboole_0(k1_xboole_0,sK4) ),
    inference(demodulation,[status(thm)],[c_18525,c_18599])).

cnf(c_35,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_625,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_47])).

cnf(c_626,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_44,negated_conjecture,
    ( v3_pre_topc(sK4,sK1)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_680,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)
    | sK4 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_626,c_44])).

cnf(c_681,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_683,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_681,c_45])).

cnf(c_1671,plain,
    ( k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_1715,plain,
    ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1671,c_567])).

cnf(c_1771,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1715])).

cnf(c_2561,plain,
    ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1715,c_46,c_1771,c_1813,c_1833])).

cnf(c_19268,plain,
    ( k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4)) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
    inference(demodulation,[status(thm)],[c_18525,c_2561])).

cnf(c_23419,plain,
    ( k1_tops_1(sK1,sK4) = k2_xboole_0(k1_xboole_0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_5856,c_5856,c_18600,c_19268])).

cnf(c_42231,plain,
    ( k1_tops_1(sK1,sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_42205,c_23419])).

cnf(c_1027,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1864,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_3176,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,sK4)
    | X0 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1864])).

cnf(c_7135,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | ~ r2_hidden(sK2,sK4)
    | k1_tops_1(sK1,sK4) != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3176])).

cnf(c_1024,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3336,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_1861,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2259,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X0,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1861])).

cnf(c_2603,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_2943,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_47])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_1933,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK3)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_2147,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3))
    | ~ r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1933])).

cnf(c_42,negated_conjecture,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_43,negated_conjecture,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f130])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42231,c_7135,c_3336,c_2943,c_2147,c_1833,c_1813,c_42,c_43,c_45,c_46])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.25/1.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.25/1.94  
% 11.25/1.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.25/1.94  
% 11.25/1.94  ------  iProver source info
% 11.25/1.94  
% 11.25/1.94  git: date: 2020-06-30 10:37:57 +0100
% 11.25/1.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.25/1.94  git: non_committed_changes: false
% 11.25/1.94  git: last_make_outside_of_git: false
% 11.25/1.94  
% 11.25/1.94  ------ 
% 11.25/1.94  
% 11.25/1.94  ------ Input Options
% 11.25/1.94  
% 11.25/1.94  --out_options                           all
% 11.25/1.94  --tptp_safe_out                         true
% 11.25/1.94  --problem_path                          ""
% 11.25/1.94  --include_path                          ""
% 11.25/1.94  --clausifier                            res/vclausify_rel
% 11.25/1.94  --clausifier_options                    ""
% 11.25/1.94  --stdin                                 false
% 11.25/1.94  --stats_out                             all
% 11.25/1.94  
% 11.25/1.94  ------ General Options
% 11.25/1.94  
% 11.25/1.94  --fof                                   false
% 11.25/1.94  --time_out_real                         305.
% 11.25/1.94  --time_out_virtual                      -1.
% 11.25/1.94  --symbol_type_check                     false
% 11.25/1.94  --clausify_out                          false
% 11.25/1.94  --sig_cnt_out                           false
% 11.25/1.94  --trig_cnt_out                          false
% 11.25/1.94  --trig_cnt_out_tolerance                1.
% 11.25/1.94  --trig_cnt_out_sk_spl                   false
% 11.25/1.94  --abstr_cl_out                          false
% 11.25/1.94  
% 11.25/1.94  ------ Global Options
% 11.25/1.94  
% 11.25/1.94  --schedule                              default
% 11.25/1.94  --add_important_lit                     false
% 11.25/1.94  --prop_solver_per_cl                    1000
% 11.25/1.94  --min_unsat_core                        false
% 11.25/1.94  --soft_assumptions                      false
% 11.25/1.94  --soft_lemma_size                       3
% 11.25/1.94  --prop_impl_unit_size                   0
% 11.25/1.94  --prop_impl_unit                        []
% 11.25/1.94  --share_sel_clauses                     true
% 11.25/1.94  --reset_solvers                         false
% 11.25/1.94  --bc_imp_inh                            [conj_cone]
% 11.25/1.94  --conj_cone_tolerance                   3.
% 11.25/1.94  --extra_neg_conj                        none
% 11.25/1.94  --large_theory_mode                     true
% 11.25/1.94  --prolific_symb_bound                   200
% 11.25/1.94  --lt_threshold                          2000
% 11.25/1.94  --clause_weak_htbl                      true
% 11.25/1.94  --gc_record_bc_elim                     false
% 11.25/1.94  
% 11.25/1.94  ------ Preprocessing Options
% 11.25/1.94  
% 11.25/1.94  --preprocessing_flag                    true
% 11.25/1.94  --time_out_prep_mult                    0.1
% 11.25/1.94  --splitting_mode                        input
% 11.25/1.94  --splitting_grd                         true
% 11.25/1.94  --splitting_cvd                         false
% 11.25/1.94  --splitting_cvd_svl                     false
% 11.25/1.94  --splitting_nvd                         32
% 11.25/1.94  --sub_typing                            true
% 11.25/1.94  --prep_gs_sim                           true
% 11.25/1.94  --prep_unflatten                        true
% 11.25/1.94  --prep_res_sim                          true
% 11.25/1.94  --prep_upred                            true
% 11.25/1.94  --prep_sem_filter                       exhaustive
% 11.25/1.94  --prep_sem_filter_out                   false
% 11.25/1.94  --pred_elim                             true
% 11.25/1.94  --res_sim_input                         true
% 11.25/1.94  --eq_ax_congr_red                       true
% 11.25/1.94  --pure_diseq_elim                       true
% 11.25/1.94  --brand_transform                       false
% 11.25/1.94  --non_eq_to_eq                          false
% 11.25/1.94  --prep_def_merge                        true
% 11.25/1.94  --prep_def_merge_prop_impl              false
% 11.25/1.94  --prep_def_merge_mbd                    true
% 11.25/1.94  --prep_def_merge_tr_red                 false
% 11.25/1.94  --prep_def_merge_tr_cl                  false
% 11.25/1.94  --smt_preprocessing                     true
% 11.25/1.94  --smt_ac_axioms                         fast
% 11.25/1.94  --preprocessed_out                      false
% 11.25/1.94  --preprocessed_stats                    false
% 11.25/1.94  
% 11.25/1.94  ------ Abstraction refinement Options
% 11.25/1.94  
% 11.25/1.94  --abstr_ref                             []
% 11.25/1.94  --abstr_ref_prep                        false
% 11.25/1.94  --abstr_ref_until_sat                   false
% 11.25/1.94  --abstr_ref_sig_restrict                funpre
% 11.25/1.94  --abstr_ref_af_restrict_to_split_sk     false
% 11.25/1.94  --abstr_ref_under                       []
% 11.25/1.94  
% 11.25/1.94  ------ SAT Options
% 11.25/1.94  
% 11.25/1.94  --sat_mode                              false
% 11.25/1.94  --sat_fm_restart_options                ""
% 11.25/1.94  --sat_gr_def                            false
% 11.25/1.94  --sat_epr_types                         true
% 11.25/1.94  --sat_non_cyclic_types                  false
% 11.25/1.94  --sat_finite_models                     false
% 11.25/1.94  --sat_fm_lemmas                         false
% 11.25/1.94  --sat_fm_prep                           false
% 11.25/1.94  --sat_fm_uc_incr                        true
% 11.25/1.94  --sat_out_model                         small
% 11.25/1.94  --sat_out_clauses                       false
% 11.25/1.94  
% 11.25/1.94  ------ QBF Options
% 11.25/1.94  
% 11.25/1.94  --qbf_mode                              false
% 11.25/1.94  --qbf_elim_univ                         false
% 11.25/1.94  --qbf_dom_inst                          none
% 11.25/1.94  --qbf_dom_pre_inst                      false
% 11.25/1.94  --qbf_sk_in                             false
% 11.25/1.94  --qbf_pred_elim                         true
% 11.25/1.94  --qbf_split                             512
% 11.25/1.94  
% 11.25/1.94  ------ BMC1 Options
% 11.25/1.94  
% 11.25/1.94  --bmc1_incremental                      false
% 11.25/1.94  --bmc1_axioms                           reachable_all
% 11.25/1.94  --bmc1_min_bound                        0
% 11.25/1.94  --bmc1_max_bound                        -1
% 11.25/1.94  --bmc1_max_bound_default                -1
% 11.25/1.94  --bmc1_symbol_reachability              true
% 11.25/1.94  --bmc1_property_lemmas                  false
% 11.25/1.94  --bmc1_k_induction                      false
% 11.25/1.94  --bmc1_non_equiv_states                 false
% 11.25/1.94  --bmc1_deadlock                         false
% 11.25/1.94  --bmc1_ucm                              false
% 11.25/1.94  --bmc1_add_unsat_core                   none
% 11.25/1.94  --bmc1_unsat_core_children              false
% 11.25/1.94  --bmc1_unsat_core_extrapolate_axioms    false
% 11.25/1.94  --bmc1_out_stat                         full
% 11.25/1.94  --bmc1_ground_init                      false
% 11.25/1.94  --bmc1_pre_inst_next_state              false
% 11.25/1.94  --bmc1_pre_inst_state                   false
% 11.25/1.94  --bmc1_pre_inst_reach_state             false
% 11.25/1.94  --bmc1_out_unsat_core                   false
% 11.25/1.94  --bmc1_aig_witness_out                  false
% 11.25/1.94  --bmc1_verbose                          false
% 11.25/1.94  --bmc1_dump_clauses_tptp                false
% 11.25/1.94  --bmc1_dump_unsat_core_tptp             false
% 11.25/1.94  --bmc1_dump_file                        -
% 11.25/1.94  --bmc1_ucm_expand_uc_limit              128
% 11.25/1.94  --bmc1_ucm_n_expand_iterations          6
% 11.25/1.94  --bmc1_ucm_extend_mode                  1
% 11.25/1.94  --bmc1_ucm_init_mode                    2
% 11.25/1.94  --bmc1_ucm_cone_mode                    none
% 11.25/1.94  --bmc1_ucm_reduced_relation_type        0
% 11.25/1.94  --bmc1_ucm_relax_model                  4
% 11.25/1.94  --bmc1_ucm_full_tr_after_sat            true
% 11.25/1.94  --bmc1_ucm_expand_neg_assumptions       false
% 11.25/1.94  --bmc1_ucm_layered_model                none
% 11.25/1.94  --bmc1_ucm_max_lemma_size               10
% 11.25/1.94  
% 11.25/1.94  ------ AIG Options
% 11.25/1.94  
% 11.25/1.94  --aig_mode                              false
% 11.25/1.94  
% 11.25/1.94  ------ Instantiation Options
% 11.25/1.94  
% 11.25/1.94  --instantiation_flag                    true
% 11.25/1.94  --inst_sos_flag                         true
% 11.25/1.94  --inst_sos_phase                        true
% 11.25/1.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.25/1.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.25/1.94  --inst_lit_sel_side                     num_symb
% 11.25/1.94  --inst_solver_per_active                1400
% 11.25/1.94  --inst_solver_calls_frac                1.
% 11.25/1.94  --inst_passive_queue_type               priority_queues
% 11.25/1.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.25/1.94  --inst_passive_queues_freq              [25;2]
% 11.25/1.94  --inst_dismatching                      true
% 11.25/1.94  --inst_eager_unprocessed_to_passive     true
% 11.25/1.94  --inst_prop_sim_given                   true
% 11.25/1.94  --inst_prop_sim_new                     false
% 11.25/1.94  --inst_subs_new                         false
% 11.25/1.94  --inst_eq_res_simp                      false
% 11.25/1.94  --inst_subs_given                       false
% 11.25/1.94  --inst_orphan_elimination               true
% 11.25/1.94  --inst_learning_loop_flag               true
% 11.25/1.94  --inst_learning_start                   3000
% 11.25/1.94  --inst_learning_factor                  2
% 11.25/1.94  --inst_start_prop_sim_after_learn       3
% 11.25/1.94  --inst_sel_renew                        solver
% 11.25/1.94  --inst_lit_activity_flag                true
% 11.25/1.94  --inst_restr_to_given                   false
% 11.25/1.94  --inst_activity_threshold               500
% 11.25/1.94  --inst_out_proof                        true
% 11.25/1.94  
% 11.25/1.94  ------ Resolution Options
% 11.25/1.94  
% 11.25/1.94  --resolution_flag                       true
% 11.25/1.94  --res_lit_sel                           adaptive
% 11.25/1.94  --res_lit_sel_side                      none
% 11.25/1.94  --res_ordering                          kbo
% 11.25/1.94  --res_to_prop_solver                    active
% 11.25/1.94  --res_prop_simpl_new                    false
% 11.25/1.94  --res_prop_simpl_given                  true
% 11.25/1.94  --res_passive_queue_type                priority_queues
% 11.25/1.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.25/1.94  --res_passive_queues_freq               [15;5]
% 11.25/1.94  --res_forward_subs                      full
% 11.25/1.94  --res_backward_subs                     full
% 11.25/1.94  --res_forward_subs_resolution           true
% 11.25/1.94  --res_backward_subs_resolution          true
% 11.25/1.94  --res_orphan_elimination                true
% 11.25/1.94  --res_time_limit                        2.
% 11.25/1.94  --res_out_proof                         true
% 11.25/1.94  
% 11.25/1.94  ------ Superposition Options
% 11.25/1.94  
% 11.25/1.94  --superposition_flag                    true
% 11.25/1.94  --sup_passive_queue_type                priority_queues
% 11.25/1.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.25/1.94  --sup_passive_queues_freq               [8;1;4]
% 11.25/1.94  --demod_completeness_check              fast
% 11.25/1.94  --demod_use_ground                      true
% 11.25/1.94  --sup_to_prop_solver                    passive
% 11.25/1.94  --sup_prop_simpl_new                    true
% 11.25/1.94  --sup_prop_simpl_given                  true
% 11.25/1.94  --sup_fun_splitting                     true
% 11.25/1.94  --sup_smt_interval                      50000
% 11.25/1.94  
% 11.25/1.94  ------ Superposition Simplification Setup
% 11.25/1.94  
% 11.25/1.94  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.25/1.94  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.25/1.94  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.25/1.94  --sup_full_triv                         [TrivRules;PropSubs]
% 11.25/1.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.25/1.94  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.25/1.94  --sup_immed_triv                        [TrivRules]
% 11.25/1.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.25/1.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.25/1.94  --sup_immed_bw_main                     []
% 11.25/1.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.25/1.94  --sup_input_triv                        [Unflattening;TrivRules]
% 11.25/1.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.25/1.94  --sup_input_bw                          []
% 11.25/1.94  
% 11.25/1.94  ------ Combination Options
% 11.25/1.94  
% 11.25/1.94  --comb_res_mult                         3
% 11.25/1.94  --comb_sup_mult                         2
% 11.25/1.94  --comb_inst_mult                        10
% 11.25/1.94  
% 11.25/1.94  ------ Debug Options
% 11.25/1.94  
% 11.25/1.94  --dbg_backtrace                         false
% 11.25/1.94  --dbg_dump_prop_clauses                 false
% 11.25/1.94  --dbg_dump_prop_clauses_file            -
% 11.25/1.94  --dbg_out_stat                          false
% 11.25/1.94  ------ Parsing...
% 11.25/1.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.25/1.94  
% 11.25/1.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.25/1.94  
% 11.25/1.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.25/1.94  
% 11.25/1.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.25/1.94  ------ Proving...
% 11.25/1.94  ------ Problem Properties 
% 11.25/1.94  
% 11.25/1.94  
% 11.25/1.94  clauses                                 45
% 11.25/1.94  conjectures                             4
% 11.25/1.94  EPR                                     7
% 11.25/1.94  Horn                                    35
% 11.25/1.94  unary                                   14
% 11.25/1.94  binary                                  17
% 11.25/1.94  lits                                    98
% 11.25/1.94  lits eq                                 24
% 11.25/1.94  fd_pure                                 0
% 11.25/1.94  fd_pseudo                               0
% 11.25/1.94  fd_cond                                 1
% 11.25/1.94  fd_pseudo_cond                          3
% 11.25/1.94  AC symbols                              0
% 11.25/1.94  
% 11.25/1.94  ------ Schedule dynamic 5 is on 
% 11.25/1.94  
% 11.25/1.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.25/1.94  
% 11.25/1.94  
% 11.25/1.94  ------ 
% 11.25/1.94  Current options:
% 11.25/1.94  ------ 
% 11.25/1.94  
% 11.25/1.94  ------ Input Options
% 11.25/1.94  
% 11.25/1.94  --out_options                           all
% 11.25/1.94  --tptp_safe_out                         true
% 11.25/1.94  --problem_path                          ""
% 11.25/1.94  --include_path                          ""
% 11.25/1.94  --clausifier                            res/vclausify_rel
% 11.25/1.94  --clausifier_options                    ""
% 11.25/1.94  --stdin                                 false
% 11.25/1.94  --stats_out                             all
% 11.25/1.94  
% 11.25/1.94  ------ General Options
% 11.25/1.94  
% 11.25/1.94  --fof                                   false
% 11.25/1.94  --time_out_real                         305.
% 11.25/1.94  --time_out_virtual                      -1.
% 11.25/1.94  --symbol_type_check                     false
% 11.25/1.94  --clausify_out                          false
% 11.25/1.94  --sig_cnt_out                           false
% 11.25/1.94  --trig_cnt_out                          false
% 11.25/1.94  --trig_cnt_out_tolerance                1.
% 11.25/1.94  --trig_cnt_out_sk_spl                   false
% 11.25/1.94  --abstr_cl_out                          false
% 11.25/1.94  
% 11.25/1.94  ------ Global Options
% 11.25/1.94  
% 11.25/1.94  --schedule                              default
% 11.25/1.94  --add_important_lit                     false
% 11.25/1.94  --prop_solver_per_cl                    1000
% 11.25/1.94  --min_unsat_core                        false
% 11.25/1.94  --soft_assumptions                      false
% 11.25/1.94  --soft_lemma_size                       3
% 11.25/1.94  --prop_impl_unit_size                   0
% 11.25/1.94  --prop_impl_unit                        []
% 11.25/1.94  --share_sel_clauses                     true
% 11.25/1.94  --reset_solvers                         false
% 11.25/1.94  --bc_imp_inh                            [conj_cone]
% 11.25/1.94  --conj_cone_tolerance                   3.
% 11.25/1.94  --extra_neg_conj                        none
% 11.25/1.94  --large_theory_mode                     true
% 11.25/1.94  --prolific_symb_bound                   200
% 11.25/1.94  --lt_threshold                          2000
% 11.25/1.94  --clause_weak_htbl                      true
% 11.25/1.94  --gc_record_bc_elim                     false
% 11.25/1.94  
% 11.25/1.94  ------ Preprocessing Options
% 11.25/1.94  
% 11.25/1.94  --preprocessing_flag                    true
% 11.25/1.94  --time_out_prep_mult                    0.1
% 11.25/1.94  --splitting_mode                        input
% 11.25/1.94  --splitting_grd                         true
% 11.25/1.94  --splitting_cvd                         false
% 11.25/1.94  --splitting_cvd_svl                     false
% 11.25/1.94  --splitting_nvd                         32
% 11.25/1.94  --sub_typing                            true
% 11.25/1.94  --prep_gs_sim                           true
% 11.25/1.94  --prep_unflatten                        true
% 11.25/1.94  --prep_res_sim                          true
% 11.25/1.94  --prep_upred                            true
% 11.25/1.94  --prep_sem_filter                       exhaustive
% 11.25/1.94  --prep_sem_filter_out                   false
% 11.25/1.94  --pred_elim                             true
% 11.25/1.94  --res_sim_input                         true
% 11.25/1.94  --eq_ax_congr_red                       true
% 11.25/1.94  --pure_diseq_elim                       true
% 11.25/1.94  --brand_transform                       false
% 11.25/1.94  --non_eq_to_eq                          false
% 11.25/1.94  --prep_def_merge                        true
% 11.25/1.94  --prep_def_merge_prop_impl              false
% 11.25/1.94  --prep_def_merge_mbd                    true
% 11.25/1.94  --prep_def_merge_tr_red                 false
% 11.25/1.94  --prep_def_merge_tr_cl                  false
% 11.25/1.94  --smt_preprocessing                     true
% 11.25/1.94  --smt_ac_axioms                         fast
% 11.25/1.94  --preprocessed_out                      false
% 11.25/1.94  --preprocessed_stats                    false
% 11.25/1.94  
% 11.25/1.94  ------ Abstraction refinement Options
% 11.25/1.94  
% 11.25/1.94  --abstr_ref                             []
% 11.25/1.94  --abstr_ref_prep                        false
% 11.25/1.94  --abstr_ref_until_sat                   false
% 11.25/1.94  --abstr_ref_sig_restrict                funpre
% 11.25/1.94  --abstr_ref_af_restrict_to_split_sk     false
% 11.25/1.94  --abstr_ref_under                       []
% 11.25/1.94  
% 11.25/1.94  ------ SAT Options
% 11.25/1.94  
% 11.25/1.94  --sat_mode                              false
% 11.25/1.94  --sat_fm_restart_options                ""
% 11.25/1.94  --sat_gr_def                            false
% 11.25/1.94  --sat_epr_types                         true
% 11.25/1.94  --sat_non_cyclic_types                  false
% 11.25/1.94  --sat_finite_models                     false
% 11.25/1.94  --sat_fm_lemmas                         false
% 11.25/1.94  --sat_fm_prep                           false
% 11.25/1.94  --sat_fm_uc_incr                        true
% 11.25/1.94  --sat_out_model                         small
% 11.25/1.94  --sat_out_clauses                       false
% 11.25/1.94  
% 11.25/1.94  ------ QBF Options
% 11.25/1.94  
% 11.25/1.94  --qbf_mode                              false
% 11.25/1.94  --qbf_elim_univ                         false
% 11.25/1.94  --qbf_dom_inst                          none
% 11.25/1.94  --qbf_dom_pre_inst                      false
% 11.25/1.94  --qbf_sk_in                             false
% 11.25/1.94  --qbf_pred_elim                         true
% 11.25/1.94  --qbf_split                             512
% 11.25/1.94  
% 11.25/1.94  ------ BMC1 Options
% 11.25/1.94  
% 11.25/1.94  --bmc1_incremental                      false
% 11.25/1.94  --bmc1_axioms                           reachable_all
% 11.25/1.94  --bmc1_min_bound                        0
% 11.25/1.94  --bmc1_max_bound                        -1
% 11.25/1.94  --bmc1_max_bound_default                -1
% 11.25/1.94  --bmc1_symbol_reachability              true
% 11.25/1.94  --bmc1_property_lemmas                  false
% 11.25/1.94  --bmc1_k_induction                      false
% 11.25/1.94  --bmc1_non_equiv_states                 false
% 11.25/1.94  --bmc1_deadlock                         false
% 11.25/1.94  --bmc1_ucm                              false
% 11.25/1.94  --bmc1_add_unsat_core                   none
% 11.25/1.94  --bmc1_unsat_core_children              false
% 11.25/1.94  --bmc1_unsat_core_extrapolate_axioms    false
% 11.25/1.94  --bmc1_out_stat                         full
% 11.25/1.94  --bmc1_ground_init                      false
% 11.25/1.94  --bmc1_pre_inst_next_state              false
% 11.25/1.94  --bmc1_pre_inst_state                   false
% 11.25/1.94  --bmc1_pre_inst_reach_state             false
% 11.25/1.94  --bmc1_out_unsat_core                   false
% 11.25/1.94  --bmc1_aig_witness_out                  false
% 11.25/1.94  --bmc1_verbose                          false
% 11.25/1.94  --bmc1_dump_clauses_tptp                false
% 11.25/1.94  --bmc1_dump_unsat_core_tptp             false
% 11.25/1.94  --bmc1_dump_file                        -
% 11.25/1.94  --bmc1_ucm_expand_uc_limit              128
% 11.25/1.94  --bmc1_ucm_n_expand_iterations          6
% 11.25/1.94  --bmc1_ucm_extend_mode                  1
% 11.25/1.94  --bmc1_ucm_init_mode                    2
% 11.25/1.94  --bmc1_ucm_cone_mode                    none
% 11.25/1.94  --bmc1_ucm_reduced_relation_type        0
% 11.25/1.94  --bmc1_ucm_relax_model                  4
% 11.25/1.94  --bmc1_ucm_full_tr_after_sat            true
% 11.25/1.94  --bmc1_ucm_expand_neg_assumptions       false
% 11.25/1.94  --bmc1_ucm_layered_model                none
% 11.25/1.94  --bmc1_ucm_max_lemma_size               10
% 11.25/1.94  
% 11.25/1.94  ------ AIG Options
% 11.25/1.94  
% 11.25/1.94  --aig_mode                              false
% 11.25/1.94  
% 11.25/1.94  ------ Instantiation Options
% 11.25/1.94  
% 11.25/1.94  --instantiation_flag                    true
% 11.25/1.94  --inst_sos_flag                         true
% 11.25/1.94  --inst_sos_phase                        true
% 11.25/1.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.25/1.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.25/1.94  --inst_lit_sel_side                     none
% 11.25/1.94  --inst_solver_per_active                1400
% 11.25/1.94  --inst_solver_calls_frac                1.
% 11.25/1.94  --inst_passive_queue_type               priority_queues
% 11.25/1.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.25/1.94  --inst_passive_queues_freq              [25;2]
% 11.25/1.94  --inst_dismatching                      true
% 11.25/1.94  --inst_eager_unprocessed_to_passive     true
% 11.25/1.94  --inst_prop_sim_given                   true
% 11.25/1.94  --inst_prop_sim_new                     false
% 11.25/1.94  --inst_subs_new                         false
% 11.25/1.94  --inst_eq_res_simp                      false
% 11.25/1.94  --inst_subs_given                       false
% 11.25/1.94  --inst_orphan_elimination               true
% 11.25/1.94  --inst_learning_loop_flag               true
% 11.25/1.94  --inst_learning_start                   3000
% 11.25/1.94  --inst_learning_factor                  2
% 11.25/1.94  --inst_start_prop_sim_after_learn       3
% 11.25/1.94  --inst_sel_renew                        solver
% 11.25/1.94  --inst_lit_activity_flag                true
% 11.25/1.94  --inst_restr_to_given                   false
% 11.25/1.94  --inst_activity_threshold               500
% 11.25/1.94  --inst_out_proof                        true
% 11.25/1.94  
% 11.25/1.94  ------ Resolution Options
% 11.25/1.94  
% 11.25/1.94  --resolution_flag                       false
% 11.25/1.94  --res_lit_sel                           adaptive
% 11.25/1.94  --res_lit_sel_side                      none
% 11.25/1.94  --res_ordering                          kbo
% 11.25/1.94  --res_to_prop_solver                    active
% 11.25/1.94  --res_prop_simpl_new                    false
% 11.25/1.94  --res_prop_simpl_given                  true
% 11.25/1.94  --res_passive_queue_type                priority_queues
% 11.25/1.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.25/1.94  --res_passive_queues_freq               [15;5]
% 11.25/1.94  --res_forward_subs                      full
% 11.25/1.94  --res_backward_subs                     full
% 11.25/1.94  --res_forward_subs_resolution           true
% 11.25/1.94  --res_backward_subs_resolution          true
% 11.25/1.94  --res_orphan_elimination                true
% 11.25/1.94  --res_time_limit                        2.
% 11.25/1.94  --res_out_proof                         true
% 11.25/1.94  
% 11.25/1.94  ------ Superposition Options
% 11.25/1.94  
% 11.25/1.94  --superposition_flag                    true
% 11.25/1.94  --sup_passive_queue_type                priority_queues
% 11.25/1.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.25/1.94  --sup_passive_queues_freq               [8;1;4]
% 11.25/1.94  --demod_completeness_check              fast
% 11.25/1.94  --demod_use_ground                      true
% 11.25/1.94  --sup_to_prop_solver                    passive
% 11.25/1.94  --sup_prop_simpl_new                    true
% 11.25/1.94  --sup_prop_simpl_given                  true
% 11.25/1.94  --sup_fun_splitting                     true
% 11.25/1.94  --sup_smt_interval                      50000
% 11.25/1.94  
% 11.25/1.94  ------ Superposition Simplification Setup
% 11.25/1.94  
% 11.25/1.94  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.25/1.94  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.25/1.94  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.25/1.94  --sup_full_triv                         [TrivRules;PropSubs]
% 11.25/1.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.25/1.94  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.25/1.94  --sup_immed_triv                        [TrivRules]
% 11.25/1.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.25/1.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.25/1.94  --sup_immed_bw_main                     []
% 11.25/1.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.25/1.94  --sup_input_triv                        [Unflattening;TrivRules]
% 11.25/1.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.25/1.94  --sup_input_bw                          []
% 11.25/1.94  
% 11.25/1.94  ------ Combination Options
% 11.25/1.94  
% 11.25/1.94  --comb_res_mult                         3
% 11.25/1.94  --comb_sup_mult                         2
% 11.25/1.94  --comb_inst_mult                        10
% 11.25/1.94  
% 11.25/1.94  ------ Debug Options
% 11.25/1.94  
% 11.25/1.94  --dbg_backtrace                         false
% 11.25/1.94  --dbg_dump_prop_clauses                 false
% 11.25/1.94  --dbg_dump_prop_clauses_file            -
% 11.25/1.94  --dbg_out_stat                          false
% 11.25/1.94  
% 11.25/1.94  
% 11.25/1.94  
% 11.25/1.94  
% 11.25/1.94  ------ Proving...
% 11.25/1.94  
% 11.25/1.94  
% 11.25/1.94  % SZS status Theorem for theBenchmark.p
% 11.25/1.94  
% 11.25/1.94  % SZS output start CNFRefutation for theBenchmark.p
% 11.25/1.94  
% 11.25/1.94  fof(f7,axiom,(
% 11.25/1.94    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f90,plain,(
% 11.25/1.94    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f7])).
% 11.25/1.94  
% 11.25/1.94  fof(f2,axiom,(
% 11.25/1.94    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f85,plain,(
% 11.25/1.94    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.25/1.94    inference(cnf_transformation,[],[f2])).
% 11.25/1.94  
% 11.25/1.94  fof(f9,axiom,(
% 11.25/1.94    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f39,plain,(
% 11.25/1.94    ! [X0,X1,X2,X3] : (X1 = X2 | (~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)))),
% 11.25/1.94    inference(ennf_transformation,[],[f9])).
% 11.25/1.94  
% 11.25/1.94  fof(f40,plain,(
% 11.25/1.94    ! [X0,X1,X2,X3] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3))),
% 11.25/1.94    inference(flattening,[],[f39])).
% 11.25/1.94  
% 11.25/1.94  fof(f92,plain,(
% 11.25/1.94    ( ! [X2,X0,X3,X1] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f40])).
% 11.25/1.94  
% 11.25/1.94  fof(f23,axiom,(
% 11.25/1.94    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f114,plain,(
% 11.25/1.94    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.25/1.94    inference(cnf_transformation,[],[f23])).
% 11.25/1.94  
% 11.25/1.94  fof(f31,axiom,(
% 11.25/1.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f62,plain,(
% 11.25/1.94    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.25/1.94    inference(ennf_transformation,[],[f31])).
% 11.25/1.94  
% 11.25/1.94  fof(f123,plain,(
% 11.25/1.94    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f62])).
% 11.25/1.94  
% 11.25/1.94  fof(f33,conjecture,(
% 11.25/1.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f34,negated_conjecture,(
% 11.25/1.94    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 11.25/1.94    inference(negated_conjecture,[],[f33])).
% 11.25/1.94  
% 11.25/1.94  fof(f65,plain,(
% 11.25/1.94    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.25/1.94    inference(ennf_transformation,[],[f34])).
% 11.25/1.94  
% 11.25/1.94  fof(f66,plain,(
% 11.25/1.94    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.25/1.94    inference(flattening,[],[f65])).
% 11.25/1.94  
% 11.25/1.94  fof(f75,plain,(
% 11.25/1.94    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.25/1.94    inference(nnf_transformation,[],[f66])).
% 11.25/1.94  
% 11.25/1.94  fof(f76,plain,(
% 11.25/1.94    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.25/1.94    inference(flattening,[],[f75])).
% 11.25/1.94  
% 11.25/1.94  fof(f77,plain,(
% 11.25/1.94    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.25/1.94    inference(rectify,[],[f76])).
% 11.25/1.94  
% 11.25/1.94  fof(f80,plain,(
% 11.25/1.94    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK4) & r1_tarski(sK4,X2) & v3_pre_topc(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.25/1.94    introduced(choice_axiom,[])).
% 11.25/1.94  
% 11.25/1.94  fof(f79,plain,(
% 11.25/1.94    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK2,k1_tops_1(X0,sK3))) & (? [X4] : (r2_hidden(sK2,X4) & r1_tarski(X4,sK3) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK2,k1_tops_1(X0,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.25/1.94    introduced(choice_axiom,[])).
% 11.25/1.94  
% 11.25/1.94  fof(f78,plain,(
% 11.25/1.94    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X1,k1_tops_1(sK1,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(X1,k1_tops_1(sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 11.25/1.94    introduced(choice_axiom,[])).
% 11.25/1.94  
% 11.25/1.94  fof(f81,plain,(
% 11.25/1.94    ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(sK2,k1_tops_1(sK1,sK3))) & ((r2_hidden(sK2,sK4) & r1_tarski(sK4,sK3) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(sK2,k1_tops_1(sK1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 11.25/1.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f77,f80,f79,f78])).
% 11.25/1.94  
% 11.25/1.94  fof(f126,plain,(
% 11.25/1.94    l1_pre_topc(sK1)),
% 11.25/1.94    inference(cnf_transformation,[],[f81])).
% 11.25/1.94  
% 11.25/1.94  fof(f26,axiom,(
% 11.25/1.94    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f54,plain,(
% 11.25/1.94    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.25/1.94    inference(ennf_transformation,[],[f26])).
% 11.25/1.94  
% 11.25/1.94  fof(f117,plain,(
% 11.25/1.94    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f54])).
% 11.25/1.94  
% 11.25/1.94  fof(f25,axiom,(
% 11.25/1.94    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f53,plain,(
% 11.25/1.94    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.25/1.94    inference(ennf_transformation,[],[f25])).
% 11.25/1.94  
% 11.25/1.94  fof(f116,plain,(
% 11.25/1.94    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f53])).
% 11.25/1.94  
% 11.25/1.94  fof(f3,axiom,(
% 11.25/1.94    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f36,plain,(
% 11.25/1.94    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.25/1.94    inference(ennf_transformation,[],[f3])).
% 11.25/1.94  
% 11.25/1.94  fof(f86,plain,(
% 11.25/1.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f36])).
% 11.25/1.94  
% 11.25/1.94  fof(f6,axiom,(
% 11.25/1.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f89,plain,(
% 11.25/1.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.25/1.94    inference(cnf_transformation,[],[f6])).
% 11.25/1.94  
% 11.25/1.94  fof(f133,plain,(
% 11.25/1.94    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.25/1.94    inference(definition_unfolding,[],[f86,f89])).
% 11.25/1.94  
% 11.25/1.94  fof(f5,axiom,(
% 11.25/1.94    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f88,plain,(
% 11.25/1.94    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.25/1.94    inference(cnf_transformation,[],[f5])).
% 11.25/1.94  
% 11.25/1.94  fof(f4,axiom,(
% 11.25/1.94    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f87,plain,(
% 11.25/1.94    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f4])).
% 11.25/1.94  
% 11.25/1.94  fof(f134,plain,(
% 11.25/1.94    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 11.25/1.94    inference(definition_unfolding,[],[f87,f89])).
% 11.25/1.94  
% 11.25/1.94  fof(f10,axiom,(
% 11.25/1.94    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f41,plain,(
% 11.25/1.94    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 11.25/1.94    inference(ennf_transformation,[],[f10])).
% 11.25/1.94  
% 11.25/1.94  fof(f93,plain,(
% 11.25/1.94    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f41])).
% 11.25/1.94  
% 11.25/1.94  fof(f128,plain,(
% 11.25/1.94    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.25/1.94    inference(cnf_transformation,[],[f81])).
% 11.25/1.94  
% 11.25/1.94  fof(f127,plain,(
% 11.25/1.94    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 11.25/1.94    inference(cnf_transformation,[],[f81])).
% 11.25/1.94  
% 11.25/1.94  fof(f132,plain,(
% 11.25/1.94    ( ! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK2,k1_tops_1(sK1,sK3))) )),
% 11.25/1.94    inference(cnf_transformation,[],[f81])).
% 11.25/1.94  
% 11.25/1.94  fof(f30,axiom,(
% 11.25/1.94    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f60,plain,(
% 11.25/1.94    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.25/1.94    inference(ennf_transformation,[],[f30])).
% 11.25/1.94  
% 11.25/1.94  fof(f61,plain,(
% 11.25/1.94    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.25/1.94    inference(flattening,[],[f60])).
% 11.25/1.94  
% 11.25/1.94  fof(f122,plain,(
% 11.25/1.94    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f61])).
% 11.25/1.94  
% 11.25/1.94  fof(f125,plain,(
% 11.25/1.94    v2_pre_topc(sK1)),
% 11.25/1.94    inference(cnf_transformation,[],[f81])).
% 11.25/1.94  
% 11.25/1.94  fof(f29,axiom,(
% 11.25/1.94    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f58,plain,(
% 11.25/1.94    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.25/1.94    inference(ennf_transformation,[],[f29])).
% 11.25/1.94  
% 11.25/1.94  fof(f59,plain,(
% 11.25/1.94    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.25/1.94    inference(flattening,[],[f58])).
% 11.25/1.94  
% 11.25/1.94  fof(f121,plain,(
% 11.25/1.94    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f59])).
% 11.25/1.94  
% 11.25/1.94  fof(f18,axiom,(
% 11.25/1.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f46,plain,(
% 11.25/1.94    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.25/1.94    inference(ennf_transformation,[],[f18])).
% 11.25/1.94  
% 11.25/1.94  fof(f109,plain,(
% 11.25/1.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.25/1.94    inference(cnf_transformation,[],[f46])).
% 11.25/1.94  
% 11.25/1.94  fof(f28,axiom,(
% 11.25/1.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f57,plain,(
% 11.25/1.94    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.25/1.94    inference(ennf_transformation,[],[f28])).
% 11.25/1.94  
% 11.25/1.94  fof(f120,plain,(
% 11.25/1.94    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f57])).
% 11.25/1.94  
% 11.25/1.94  fof(f16,axiom,(
% 11.25/1.94    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f104,plain,(
% 11.25/1.94    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 11.25/1.94    inference(cnf_transformation,[],[f16])).
% 11.25/1.94  
% 11.25/1.94  fof(f12,axiom,(
% 11.25/1.94    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f95,plain,(
% 11.25/1.94    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f12])).
% 11.25/1.94  
% 11.25/1.94  fof(f141,plain,(
% 11.25/1.94    ( ! [X0] : (r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0))) )),
% 11.25/1.94    inference(definition_unfolding,[],[f104,f95])).
% 11.25/1.94  
% 11.25/1.94  fof(f15,axiom,(
% 11.25/1.94    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f44,plain,(
% 11.25/1.94    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 11.25/1.94    inference(ennf_transformation,[],[f15])).
% 11.25/1.94  
% 11.25/1.94  fof(f103,plain,(
% 11.25/1.94    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f44])).
% 11.25/1.94  
% 11.25/1.94  fof(f140,plain,(
% 11.25/1.94    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 11.25/1.94    inference(definition_unfolding,[],[f103,f95])).
% 11.25/1.94  
% 11.25/1.94  fof(f14,axiom,(
% 11.25/1.94    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f43,plain,(
% 11.25/1.94    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 11.25/1.94    inference(ennf_transformation,[],[f14])).
% 11.25/1.94  
% 11.25/1.94  fof(f72,plain,(
% 11.25/1.94    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 11.25/1.94    inference(nnf_transformation,[],[f43])).
% 11.25/1.94  
% 11.25/1.94  fof(f73,plain,(
% 11.25/1.94    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 11.25/1.94    inference(flattening,[],[f72])).
% 11.25/1.94  
% 11.25/1.94  fof(f101,plain,(
% 11.25/1.94    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 11.25/1.94    inference(cnf_transformation,[],[f73])).
% 11.25/1.94  
% 11.25/1.94  fof(f137,plain,(
% 11.25/1.94    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) != X0) )),
% 11.25/1.94    inference(definition_unfolding,[],[f101,f95])).
% 11.25/1.94  
% 11.25/1.94  fof(f144,plain,(
% 11.25/1.94    ( ! [X2,X1] : (r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 11.25/1.94    inference(equality_resolution,[],[f137])).
% 11.25/1.94  
% 11.25/1.94  fof(f1,axiom,(
% 11.25/1.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f35,plain,(
% 11.25/1.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.25/1.94    inference(ennf_transformation,[],[f1])).
% 11.25/1.94  
% 11.25/1.94  fof(f67,plain,(
% 11.25/1.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.25/1.94    inference(nnf_transformation,[],[f35])).
% 11.25/1.94  
% 11.25/1.94  fof(f68,plain,(
% 11.25/1.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.25/1.94    inference(rectify,[],[f67])).
% 11.25/1.94  
% 11.25/1.94  fof(f69,plain,(
% 11.25/1.94    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.25/1.94    introduced(choice_axiom,[])).
% 11.25/1.94  
% 11.25/1.94  fof(f70,plain,(
% 11.25/1.94    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.25/1.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f68,f69])).
% 11.25/1.94  
% 11.25/1.94  fof(f83,plain,(
% 11.25/1.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f70])).
% 11.25/1.94  
% 11.25/1.94  fof(f84,plain,(
% 11.25/1.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f70])).
% 11.25/1.94  
% 11.25/1.94  fof(f8,axiom,(
% 11.25/1.94    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f37,plain,(
% 11.25/1.94    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 11.25/1.94    inference(ennf_transformation,[],[f8])).
% 11.25/1.94  
% 11.25/1.94  fof(f38,plain,(
% 11.25/1.94    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 11.25/1.94    inference(flattening,[],[f37])).
% 11.25/1.94  
% 11.25/1.94  fof(f91,plain,(
% 11.25/1.94    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f38])).
% 11.25/1.94  
% 11.25/1.94  fof(f13,axiom,(
% 11.25/1.94    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f71,plain,(
% 11.25/1.94    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.25/1.94    inference(nnf_transformation,[],[f13])).
% 11.25/1.94  
% 11.25/1.94  fof(f96,plain,(
% 11.25/1.94    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f71])).
% 11.25/1.94  
% 11.25/1.94  fof(f136,plain,(
% 11.25/1.94    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) != k2_tarski(X0,X0)) )),
% 11.25/1.94    inference(definition_unfolding,[],[f96,f95,f95,f95])).
% 11.25/1.94  
% 11.25/1.94  fof(f142,plain,(
% 11.25/1.94    ( ! [X1] : (k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) != k2_tarski(X1,X1)) )),
% 11.25/1.94    inference(equality_resolution,[],[f136])).
% 11.25/1.94  
% 11.25/1.94  fof(f82,plain,(
% 11.25/1.94    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f70])).
% 11.25/1.94  
% 11.25/1.94  fof(f17,axiom,(
% 11.25/1.94    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f45,plain,(
% 11.25/1.94    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.25/1.94    inference(ennf_transformation,[],[f17])).
% 11.25/1.94  
% 11.25/1.94  fof(f74,plain,(
% 11.25/1.94    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.25/1.94    inference(nnf_transformation,[],[f45])).
% 11.25/1.94  
% 11.25/1.94  fof(f106,plain,(
% 11.25/1.94    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f74])).
% 11.25/1.94  
% 11.25/1.94  fof(f19,axiom,(
% 11.25/1.94    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f110,plain,(
% 11.25/1.94    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.25/1.94    inference(cnf_transformation,[],[f19])).
% 11.25/1.94  
% 11.25/1.94  fof(f21,axiom,(
% 11.25/1.94    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f49,plain,(
% 11.25/1.94    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.25/1.94    inference(ennf_transformation,[],[f21])).
% 11.25/1.94  
% 11.25/1.94  fof(f112,plain,(
% 11.25/1.94    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.25/1.94    inference(cnf_transformation,[],[f49])).
% 11.25/1.94  
% 11.25/1.94  fof(f22,axiom,(
% 11.25/1.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f50,plain,(
% 11.25/1.94    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.25/1.94    inference(ennf_transformation,[],[f22])).
% 11.25/1.94  
% 11.25/1.94  fof(f113,plain,(
% 11.25/1.94    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.25/1.94    inference(cnf_transformation,[],[f50])).
% 11.25/1.94  
% 11.25/1.94  fof(f20,axiom,(
% 11.25/1.94    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f47,plain,(
% 11.25/1.94    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.25/1.94    inference(ennf_transformation,[],[f20])).
% 11.25/1.94  
% 11.25/1.94  fof(f48,plain,(
% 11.25/1.94    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.25/1.94    inference(flattening,[],[f47])).
% 11.25/1.94  
% 11.25/1.94  fof(f111,plain,(
% 11.25/1.94    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.25/1.94    inference(cnf_transformation,[],[f48])).
% 11.25/1.94  
% 11.25/1.94  fof(f27,axiom,(
% 11.25/1.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f55,plain,(
% 11.25/1.94    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0))) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.25/1.94    inference(ennf_transformation,[],[f27])).
% 11.25/1.94  
% 11.25/1.94  fof(f56,plain,(
% 11.25/1.94    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0)) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.25/1.94    inference(flattening,[],[f55])).
% 11.25/1.94  
% 11.25/1.94  fof(f118,plain,(
% 11.25/1.94    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f56])).
% 11.25/1.94  
% 11.25/1.94  fof(f129,plain,(
% 11.25/1.94    v3_pre_topc(sK4,sK1) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.25/1.94    inference(cnf_transformation,[],[f81])).
% 11.25/1.94  
% 11.25/1.94  fof(f32,axiom,(
% 11.25/1.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.25/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.94  
% 11.25/1.94  fof(f63,plain,(
% 11.25/1.94    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.25/1.94    inference(ennf_transformation,[],[f32])).
% 11.25/1.94  
% 11.25/1.94  fof(f64,plain,(
% 11.25/1.94    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.25/1.94    inference(flattening,[],[f63])).
% 11.25/1.94  
% 11.25/1.94  fof(f124,plain,(
% 11.25/1.94    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.25/1.94    inference(cnf_transformation,[],[f64])).
% 11.25/1.94  
% 11.25/1.94  fof(f131,plain,(
% 11.25/1.94    r2_hidden(sK2,sK4) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.25/1.94    inference(cnf_transformation,[],[f81])).
% 11.25/1.94  
% 11.25/1.94  fof(f130,plain,(
% 11.25/1.94    r1_tarski(sK4,sK3) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.25/1.94    inference(cnf_transformation,[],[f81])).
% 11.25/1.94  
% 11.25/1.94  cnf(c_7,plain,
% 11.25/1.94      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.25/1.94      inference(cnf_transformation,[],[f90]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1703,plain,
% 11.25/1.94      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_3,plain,
% 11.25/1.94      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.25/1.94      inference(cnf_transformation,[],[f85]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_9,plain,
% 11.25/1.94      ( ~ r1_xboole_0(X0,X1)
% 11.25/1.94      | ~ r1_xboole_0(X2,X3)
% 11.25/1.94      | X2 = X1
% 11.25/1.94      | k2_xboole_0(X2,X0) != k2_xboole_0(X3,X1) ),
% 11.25/1.94      inference(cnf_transformation,[],[f92]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1701,plain,
% 11.25/1.94      ( X0 = X1
% 11.25/1.94      | k2_xboole_0(X0,X2) != k2_xboole_0(X3,X1)
% 11.25/1.94      | r1_xboole_0(X2,X1) != iProver_top
% 11.25/1.94      | r1_xboole_0(X0,X3) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_6912,plain,
% 11.25/1.94      ( X0 = X1
% 11.25/1.94      | k2_xboole_0(X2,X0) != X1
% 11.25/1.94      | r1_xboole_0(X1,X2) != iProver_top
% 11.25/1.94      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_3,c_1701]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_7057,plain,
% 11.25/1.94      ( k2_xboole_0(X0,X1) = X1
% 11.25/1.94      | r1_xboole_0(k2_xboole_0(X0,X1),X0) != iProver_top
% 11.25/1.94      | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
% 11.25/1.94      inference(equality_resolution,[status(thm)],[c_6912]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_42190,plain,
% 11.25/1.94      ( k2_xboole_0(k1_xboole_0,X0) = X0
% 11.25/1.94      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_1703,c_7057]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_30,plain,
% 11.25/1.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.25/1.94      inference(cnf_transformation,[],[f114]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1682,plain,
% 11.25/1.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_39,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.25/1.94      | ~ l1_pre_topc(X1) ),
% 11.25/1.94      inference(cnf_transformation,[],[f123]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_47,negated_conjecture,
% 11.25/1.94      ( l1_pre_topc(sK1) ),
% 11.25/1.94      inference(cnf_transformation,[],[f126]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_589,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.25/1.94      | sK1 != X1 ),
% 11.25/1.94      inference(resolution_lifted,[status(thm)],[c_39,c_47]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_590,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 11.25/1.94      inference(unflattening,[status(thm)],[c_589]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1675,plain,
% 11.25/1.94      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.25/1.94      | r1_tarski(k1_tops_1(sK1,X0),X0) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_33,plain,
% 11.25/1.94      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 11.25/1.94      inference(cnf_transformation,[],[f117]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_32,plain,
% 11.25/1.94      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.25/1.94      inference(cnf_transformation,[],[f116]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_506,plain,
% 11.25/1.94      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.25/1.94      inference(resolution,[status(thm)],[c_33,c_32]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_566,plain,
% 11.25/1.94      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 11.25/1.94      inference(resolution_lifted,[status(thm)],[c_506,c_47]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_567,plain,
% 11.25/1.94      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 11.25/1.94      inference(unflattening,[status(thm)],[c_566]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1712,plain,
% 11.25/1.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 11.25/1.94      | r1_tarski(k1_tops_1(sK1,X0),X0) = iProver_top ),
% 11.25/1.94      inference(light_normalisation,[status(thm)],[c_1675,c_567]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_2628,plain,
% 11.25/1.94      ( r1_tarski(k1_tops_1(sK1,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_1682,c_1712]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_4,plain,
% 11.25/1.94      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.25/1.94      inference(cnf_transformation,[],[f133]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1704,plain,
% 11.25/1.94      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 11.25/1.94      | r1_tarski(X0,X1) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_4840,plain,
% 11.25/1.94      ( k4_xboole_0(k1_tops_1(sK1,k1_xboole_0),k4_xboole_0(k1_tops_1(sK1,k1_xboole_0),k1_xboole_0)) = k1_tops_1(sK1,k1_xboole_0) ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_2628,c_1704]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_6,plain,
% 11.25/1.94      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.25/1.94      inference(cnf_transformation,[],[f88]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_5,plain,
% 11.25/1.94      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.25/1.94      inference(cnf_transformation,[],[f134]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1709,plain,
% 11.25/1.94      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.25/1.94      inference(light_normalisation,[status(thm)],[c_5,c_6]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_4843,plain,
% 11.25/1.94      ( k1_tops_1(sK1,k1_xboole_0) = k1_xboole_0 ),
% 11.25/1.94      inference(demodulation,[status(thm)],[c_4840,c_6,c_1709]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_5187,plain,
% 11.25/1.94      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.25/1.94      inference(demodulation,[status(thm)],[c_4843,c_2628]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_10,plain,
% 11.25/1.94      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 11.25/1.94      inference(cnf_transformation,[],[f93]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1700,plain,
% 11.25/1.94      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 11.25/1.94      | r1_tarski(X0,X2) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_4583,plain,
% 11.25/1.94      ( r1_xboole_0(X0,X1) = iProver_top
% 11.25/1.94      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_6,c_1700]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_7685,plain,
% 11.25/1.94      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_5187,c_4583]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_42205,plain,
% 11.25/1.94      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.25/1.94      inference(global_propositional_subsumption,
% 11.25/1.94                [status(thm)],
% 11.25/1.94                [c_42190,c_7685]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_45,negated_conjecture,
% 11.25/1.94      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 11.25/1.94      inference(cnf_transformation,[],[f128]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1678,plain,
% 11.25/1.94      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1711,plain,
% 11.25/1.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.25/1.94      inference(light_normalisation,[status(thm)],[c_1678,c_567]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_46,negated_conjecture,
% 11.25/1.94      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.25/1.94      inference(cnf_transformation,[],[f127]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_51,plain,
% 11.25/1.94      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1813,plain,
% 11.25/1.94      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_590]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1814,plain,
% 11.25/1.94      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.25/1.94      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_1813]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_41,negated_conjecture,
% 11.25/1.94      ( ~ v3_pre_topc(X0,sK1)
% 11.25/1.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ r2_hidden(sK2,X0)
% 11.25/1.94      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | ~ r1_tarski(X0,sK3) ),
% 11.25/1.94      inference(cnf_transformation,[],[f132]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_38,plain,
% 11.25/1.94      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.25/1.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.25/1.94      | ~ v2_pre_topc(X0)
% 11.25/1.94      | ~ l1_pre_topc(X0) ),
% 11.25/1.94      inference(cnf_transformation,[],[f122]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_48,negated_conjecture,
% 11.25/1.94      ( v2_pre_topc(sK1) ),
% 11.25/1.94      inference(cnf_transformation,[],[f125]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_520,plain,
% 11.25/1.94      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.25/1.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.25/1.94      | ~ l1_pre_topc(X0)
% 11.25/1.94      | sK1 != X0 ),
% 11.25/1.94      inference(resolution_lifted,[status(thm)],[c_38,c_48]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_521,plain,
% 11.25/1.94      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 11.25/1.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ l1_pre_topc(sK1) ),
% 11.25/1.94      inference(unflattening,[status(thm)],[c_520]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_525,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
% 11.25/1.94      inference(global_propositional_subsumption,
% 11.25/1.94                [status(thm)],
% 11.25/1.94                [c_521,c_47]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_526,plain,
% 11.25/1.94      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 11.25/1.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.25/1.94      inference(renaming,[status(thm)],[c_525]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_714,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ r2_hidden(sK2,X0)
% 11.25/1.94      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | ~ r1_tarski(X0,sK3)
% 11.25/1.94      | k1_tops_1(sK1,X1) != X0
% 11.25/1.94      | sK1 != sK1 ),
% 11.25/1.94      inference(resolution_lifted,[status(thm)],[c_41,c_526]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_715,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 11.25/1.94      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
% 11.25/1.94      inference(unflattening,[status(thm)],[c_714]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_37,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | ~ l1_pre_topc(X1) ),
% 11.25/1.94      inference(cnf_transformation,[],[f121]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_601,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | sK1 != X1 ),
% 11.25/1.94      inference(resolution_lifted,[status(thm)],[c_37,c_47]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_602,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.25/1.94      inference(unflattening,[status(thm)],[c_601]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_719,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 11.25/1.94      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
% 11.25/1.94      inference(global_propositional_subsumption,
% 11.25/1.94                [status(thm)],
% 11.25/1.94                [c_715,c_602]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1833,plain,
% 11.25/1.94      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_719]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1834,plain,
% 11.25/1.94      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
% 11.25/1.94      | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_1833]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_2540,plain,
% 11.25/1.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 11.25/1.94      inference(global_propositional_subsumption,
% 11.25/1.94                [status(thm)],
% 11.25/1.94                [c_1711,c_51,c_1814,c_1834]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_25,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.25/1.94      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.25/1.94      inference(cnf_transformation,[],[f109]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1687,plain,
% 11.25/1.94      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.25/1.94      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_5637,plain,
% 11.25/1.94      ( k3_subset_1(k2_struct_0(sK1),sK4) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_2540,c_1687]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_36,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | ~ l1_pre_topc(X1)
% 11.25/1.94      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 11.25/1.94      inference(cnf_transformation,[],[f120]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_613,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 11.25/1.94      | sK1 != X1 ),
% 11.25/1.94      inference(resolution_lifted,[status(thm)],[c_36,c_47]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_614,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
% 11.25/1.94      inference(unflattening,[status(thm)],[c_613]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1673,plain,
% 11.25/1.94      ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
% 11.25/1.94      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1714,plain,
% 11.25/1.94      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
% 11.25/1.94      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 11.25/1.94      inference(light_normalisation,[status(thm)],[c_1673,c_567]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_2546,plain,
% 11.25/1.94      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_2540,c_1714]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_5856,plain,
% 11.25/1.94      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
% 11.25/1.94      inference(demodulation,[status(thm)],[c_5637,c_2546]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_20,plain,
% 11.25/1.94      ( r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
% 11.25/1.94      inference(cnf_transformation,[],[f141]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1692,plain,
% 11.25/1.94      ( r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_19,plain,
% 11.25/1.94      ( r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1) ),
% 11.25/1.94      inference(cnf_transformation,[],[f140]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1693,plain,
% 11.25/1.94      ( r1_xboole_0(k2_tarski(X0,X0),X1) = iProver_top
% 11.25/1.94      | r2_hidden(X0,X1) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_15,plain,
% 11.25/1.94      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) ),
% 11.25/1.94      inference(cnf_transformation,[],[f144]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1697,plain,
% 11.25/1.94      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1,plain,
% 11.25/1.94      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.25/1.94      inference(cnf_transformation,[],[f83]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1706,plain,
% 11.25/1.94      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.25/1.94      | r1_tarski(X0,X1) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_0,plain,
% 11.25/1.94      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.25/1.94      inference(cnf_transformation,[],[f84]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1707,plain,
% 11.25/1.94      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.25/1.94      | r1_tarski(X0,X1) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_5510,plain,
% 11.25/1.94      ( r1_tarski(X0,X0) = iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_1706,c_1707]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_8,plain,
% 11.25/1.94      ( ~ r1_xboole_0(X0,X1)
% 11.25/1.94      | ~ r1_tarski(X2,X0)
% 11.25/1.94      | ~ r1_tarski(X2,X1)
% 11.25/1.94      | k1_xboole_0 = X2 ),
% 11.25/1.94      inference(cnf_transformation,[],[f91]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1702,plain,
% 11.25/1.94      ( k1_xboole_0 = X0
% 11.25/1.94      | r1_xboole_0(X1,X2) != iProver_top
% 11.25/1.94      | r1_tarski(X0,X1) != iProver_top
% 11.25/1.94      | r1_tarski(X0,X2) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_7720,plain,
% 11.25/1.94      ( k1_xboole_0 = X0
% 11.25/1.94      | r1_xboole_0(X1,X0) != iProver_top
% 11.25/1.94      | r1_tarski(X0,X1) != iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_5510,c_1702]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_14961,plain,
% 11.25/1.94      ( k2_tarski(X0,X0) = k1_xboole_0
% 11.25/1.94      | r1_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0)) != iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_1697,c_7720]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_13,plain,
% 11.25/1.94      ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) != k2_tarski(X0,X0) ),
% 11.25/1.94      inference(cnf_transformation,[],[f142]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1710,plain,
% 11.25/1.94      ( k2_tarski(X0,X0) != k1_xboole_0 ),
% 11.25/1.94      inference(demodulation,[status(thm)],[c_13,c_1709]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_15216,plain,
% 11.25/1.94      ( r1_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0)) != iProver_top ),
% 11.25/1.94      inference(global_propositional_subsumption,
% 11.25/1.94                [status(thm)],
% 11.25/1.94                [c_14961,c_1710]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_15217,plain,
% 11.25/1.94      ( r1_xboole_0(k2_tarski(X0,X1),k2_tarski(X1,X1)) != iProver_top ),
% 11.25/1.94      inference(renaming,[status(thm)],[c_15216]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_15222,plain,
% 11.25/1.94      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_1693,c_15217]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_2,plain,
% 11.25/1.94      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.25/1.94      inference(cnf_transformation,[],[f82]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1705,plain,
% 11.25/1.94      ( r2_hidden(X0,X1) != iProver_top
% 11.25/1.94      | r2_hidden(X0,X2) = iProver_top
% 11.25/1.94      | r1_tarski(X1,X2) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_15804,plain,
% 11.25/1.94      ( r2_hidden(X0,X1) = iProver_top
% 11.25/1.94      | r1_tarski(k2_tarski(X0,X0),X1) != iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_15222,c_1705]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_15979,plain,
% 11.25/1.94      ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_1692,c_15804]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_23,plain,
% 11.25/1.94      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.25/1.94      inference(cnf_transformation,[],[f106]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1689,plain,
% 11.25/1.94      ( m1_subset_1(X0,X1) = iProver_top
% 11.25/1.94      | r2_hidden(X0,X1) != iProver_top
% 11.25/1.94      | v1_xboole_0(X1) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_15988,plain,
% 11.25/1.94      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 11.25/1.94      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_15979,c_1689]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_26,plain,
% 11.25/1.94      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.25/1.94      inference(cnf_transformation,[],[f110]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_101,plain,
% 11.25/1.94      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_18517,plain,
% 11.25/1.94      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.25/1.94      inference(global_propositional_subsumption,
% 11.25/1.94                [status(thm)],
% 11.25/1.94                [c_15988,c_101]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_28,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.25/1.94      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.25/1.94      inference(cnf_transformation,[],[f112]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1684,plain,
% 11.25/1.94      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 11.25/1.94      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_18525,plain,
% 11.25/1.94      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_18517,c_1684]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_18526,plain,
% 11.25/1.94      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_18517,c_1687]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_18593,plain,
% 11.25/1.94      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 11.25/1.94      inference(light_normalisation,[status(thm)],[c_18526,c_1709]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_29,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.25/1.94      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.25/1.94      | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
% 11.25/1.94      inference(cnf_transformation,[],[f113]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1683,plain,
% 11.25/1.94      ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
% 11.25/1.94      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 11.25/1.94      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_2898,plain,
% 11.25/1.94      ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),X0),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),X0,sK4))
% 11.25/1.94      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_2540,c_1683]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_18570,plain,
% 11.25/1.94      ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_struct_0(sK1)),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_18517,c_2898]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_18595,plain,
% 11.25/1.94      ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) ),
% 11.25/1.94      inference(demodulation,[status(thm)],[c_18593,c_18570]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_27,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.25/1.94      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.25/1.94      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 11.25/1.94      inference(cnf_transformation,[],[f111]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1685,plain,
% 11.25/1.94      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.25/1.94      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 11.25/1.94      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_3793,plain,
% 11.25/1.94      ( k4_subset_1(k2_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
% 11.25/1.94      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_2540,c_1685]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_4228,plain,
% 11.25/1.94      ( k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) = k2_xboole_0(k1_xboole_0,sK4) ),
% 11.25/1.94      inference(superposition,[status(thm)],[c_1682,c_3793]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_18599,plain,
% 11.25/1.94      ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k2_xboole_0(k1_xboole_0,sK4) ),
% 11.25/1.94      inference(light_normalisation,[status(thm)],[c_18595,c_4228]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_18600,plain,
% 11.25/1.94      ( k3_subset_1(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK4)) = k2_xboole_0(k1_xboole_0,sK4) ),
% 11.25/1.94      inference(demodulation,[status(thm)],[c_18525,c_18599]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_35,plain,
% 11.25/1.94      ( ~ v3_pre_topc(X0,X1)
% 11.25/1.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | ~ l1_pre_topc(X1)
% 11.25/1.94      | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ),
% 11.25/1.94      inference(cnf_transformation,[],[f118]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_625,plain,
% 11.25/1.94      ( ~ v3_pre_topc(X0,X1)
% 11.25/1.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)
% 11.25/1.94      | sK1 != X1 ),
% 11.25/1.94      inference(resolution_lifted,[status(thm)],[c_35,c_47]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_626,plain,
% 11.25/1.94      ( ~ v3_pre_topc(X0,sK1)
% 11.25/1.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0) ),
% 11.25/1.94      inference(unflattening,[status(thm)],[c_625]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_44,negated_conjecture,
% 11.25/1.94      ( v3_pre_topc(sK4,sK1) | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 11.25/1.94      inference(cnf_transformation,[],[f129]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_680,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)
% 11.25/1.94      | sK4 != X0
% 11.25/1.94      | sK1 != sK1 ),
% 11.25/1.94      inference(resolution_lifted,[status(thm)],[c_626,c_44]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_681,plain,
% 11.25/1.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 11.25/1.94      inference(unflattening,[status(thm)],[c_680]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_683,plain,
% 11.25/1.94      ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 11.25/1.94      inference(global_propositional_subsumption,
% 11.25/1.94                [status(thm)],
% 11.25/1.94                [c_681,c_45]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1671,plain,
% 11.25/1.94      ( k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.25/1.94      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1715,plain,
% 11.25/1.94      ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.25/1.94      inference(light_normalisation,[status(thm)],[c_1671,c_567]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1771,plain,
% 11.25/1.94      ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 11.25/1.94      inference(predicate_to_equality_rev,[status(thm)],[c_1715]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_2561,plain,
% 11.25/1.94      ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 11.25/1.94      inference(global_propositional_subsumption,
% 11.25/1.94                [status(thm)],
% 11.25/1.94                [c_1715,c_46,c_1771,c_1813,c_1833]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_19268,plain,
% 11.25/1.94      ( k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4)) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
% 11.25/1.94      inference(demodulation,[status(thm)],[c_18525,c_2561]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_23419,plain,
% 11.25/1.94      ( k1_tops_1(sK1,sK4) = k2_xboole_0(k1_xboole_0,sK4) ),
% 11.25/1.94      inference(light_normalisation,
% 11.25/1.94                [status(thm)],
% 11.25/1.94                [c_5856,c_5856,c_18600,c_19268]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_42231,plain,
% 11.25/1.94      ( k1_tops_1(sK1,sK4) = sK4 ),
% 11.25/1.94      inference(demodulation,[status(thm)],[c_42205,c_23419]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1027,plain,
% 11.25/1.94      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.25/1.94      theory(equality) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1864,plain,
% 11.25/1.94      ( ~ r2_hidden(X0,X1) | r2_hidden(sK2,X2) | X2 != X1 | sK2 != X0 ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_1027]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_3176,plain,
% 11.25/1.94      ( r2_hidden(sK2,X0)
% 11.25/1.94      | ~ r2_hidden(sK2,sK4)
% 11.25/1.94      | X0 != sK4
% 11.25/1.94      | sK2 != sK2 ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_1864]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_7135,plain,
% 11.25/1.94      ( r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 11.25/1.94      | ~ r2_hidden(sK2,sK4)
% 11.25/1.94      | k1_tops_1(sK1,sK4) != sK4
% 11.25/1.94      | sK2 != sK2 ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_3176]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1024,plain,( X0 = X0 ),theory(equality) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_3336,plain,
% 11.25/1.94      ( sK2 = sK2 ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_1024]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1861,plain,
% 11.25/1.94      ( ~ r2_hidden(sK2,X0) | r2_hidden(sK2,X1) | ~ r1_tarski(X0,X1) ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_2]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_2259,plain,
% 11.25/1.94      ( ~ r2_hidden(sK2,X0)
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | ~ r1_tarski(X0,k1_tops_1(sK1,sK3)) ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_1861]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_2603,plain,
% 11.25/1.94      ( ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | ~ r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_2259]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_2943,plain,
% 11.25/1.94      ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 11.25/1.94      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.25/1.94      | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_2603]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_40,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | ~ r1_tarski(X0,X2)
% 11.25/1.94      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.25/1.94      | ~ l1_pre_topc(X1) ),
% 11.25/1.94      inference(cnf_transformation,[],[f124]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_571,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.25/1.94      | ~ r1_tarski(X0,X2)
% 11.25/1.94      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.25/1.94      | sK1 != X1 ),
% 11.25/1.94      inference(resolution_lifted,[status(thm)],[c_40,c_47]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_572,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ r1_tarski(X1,X0)
% 11.25/1.94      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 11.25/1.94      inference(unflattening,[status(thm)],[c_571]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_1933,plain,
% 11.25/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ r1_tarski(X0,sK3)
% 11.25/1.94      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_572]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_2147,plain,
% 11.25/1.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.25/1.94      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3))
% 11.25/1.94      | ~ r1_tarski(sK4,sK3) ),
% 11.25/1.94      inference(instantiation,[status(thm)],[c_1933]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_42,negated_conjecture,
% 11.25/1.94      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r2_hidden(sK2,sK4) ),
% 11.25/1.94      inference(cnf_transformation,[],[f131]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(c_43,negated_conjecture,
% 11.25/1.94      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r1_tarski(sK4,sK3) ),
% 11.25/1.94      inference(cnf_transformation,[],[f130]) ).
% 11.25/1.94  
% 11.25/1.94  cnf(contradiction,plain,
% 11.25/1.94      ( $false ),
% 11.25/1.94      inference(minisat,
% 11.25/1.94                [status(thm)],
% 11.25/1.94                [c_42231,c_7135,c_3336,c_2943,c_2147,c_1833,c_1813,c_42,
% 11.25/1.94                 c_43,c_45,c_46]) ).
% 11.25/1.94  
% 11.25/1.94  
% 11.25/1.94  % SZS output end CNFRefutation for theBenchmark.p
% 11.25/1.94  
% 11.25/1.94  ------                               Statistics
% 11.25/1.94  
% 11.25/1.94  ------ General
% 11.25/1.94  
% 11.25/1.94  abstr_ref_over_cycles:                  0
% 11.25/1.94  abstr_ref_under_cycles:                 0
% 11.25/1.94  gc_basic_clause_elim:                   0
% 11.25/1.94  forced_gc_time:                         0
% 11.25/1.94  parsing_time:                           0.011
% 11.25/1.94  unif_index_cands_time:                  0.
% 11.25/1.94  unif_index_add_time:                    0.
% 11.25/1.94  orderings_time:                         0.
% 11.25/1.94  out_proof_time:                         0.018
% 11.25/1.94  total_time:                             1.252
% 11.25/1.94  num_of_symbols:                         57
% 11.25/1.94  num_of_terms:                           27212
% 11.25/1.94  
% 11.25/1.94  ------ Preprocessing
% 11.25/1.94  
% 11.25/1.94  num_of_splits:                          0
% 11.25/1.94  num_of_split_atoms:                     0
% 11.25/1.94  num_of_reused_defs:                     0
% 11.25/1.94  num_eq_ax_congr_red:                    25
% 11.25/1.94  num_of_sem_filtered_clauses:            1
% 11.25/1.94  num_of_subtypes:                        0
% 11.25/1.94  monotx_restored_types:                  0
% 11.25/1.94  sat_num_of_epr_types:                   0
% 11.25/1.94  sat_num_of_non_cyclic_types:            0
% 11.25/1.94  sat_guarded_non_collapsed_types:        0
% 11.25/1.94  num_pure_diseq_elim:                    0
% 11.25/1.94  simp_replaced_by:                       0
% 11.25/1.94  res_preprocessed:                       219
% 11.25/1.94  prep_upred:                             0
% 11.25/1.94  prep_unflattend:                        12
% 11.25/1.94  smt_new_axioms:                         0
% 11.25/1.94  pred_elim_cands:                        5
% 11.25/1.94  pred_elim:                              4
% 11.25/1.94  pred_elim_cl:                           4
% 11.25/1.94  pred_elim_cycles:                       6
% 11.25/1.94  merged_defs:                            0
% 11.25/1.94  merged_defs_ncl:                        0
% 11.25/1.94  bin_hyper_res:                          0
% 11.25/1.94  prep_cycles:                            4
% 11.25/1.94  pred_elim_time:                         0.007
% 11.25/1.94  splitting_time:                         0.
% 11.25/1.94  sem_filter_time:                        0.
% 11.25/1.94  monotx_time:                            0.001
% 11.25/1.94  subtype_inf_time:                       0.
% 11.25/1.94  
% 11.25/1.94  ------ Problem properties
% 11.25/1.94  
% 11.25/1.94  clauses:                                45
% 11.25/1.94  conjectures:                            4
% 11.25/1.94  epr:                                    7
% 11.25/1.94  horn:                                   35
% 11.25/1.94  ground:                                 6
% 11.25/1.94  unary:                                  14
% 11.25/1.94  binary:                                 17
% 11.25/1.94  lits:                                   98
% 11.25/1.94  lits_eq:                                24
% 11.25/1.94  fd_pure:                                0
% 11.25/1.94  fd_pseudo:                              0
% 11.25/1.94  fd_cond:                                1
% 11.25/1.94  fd_pseudo_cond:                         3
% 11.25/1.94  ac_symbols:                             0
% 11.25/1.94  
% 11.25/1.94  ------ Propositional Solver
% 11.25/1.94  
% 11.25/1.94  prop_solver_calls:                      31
% 11.25/1.94  prop_fast_solver_calls:                 2136
% 11.25/1.94  smt_solver_calls:                       0
% 11.25/1.94  smt_fast_solver_calls:                  0
% 11.25/1.94  prop_num_of_clauses:                    17287
% 11.25/1.94  prop_preprocess_simplified:             33751
% 11.25/1.94  prop_fo_subsumed:                       40
% 11.25/1.94  prop_solver_time:                       0.
% 11.25/1.94  smt_solver_time:                        0.
% 11.25/1.94  smt_fast_solver_time:                   0.
% 11.25/1.94  prop_fast_solver_time:                  0.
% 11.25/1.94  prop_unsat_core_time:                   0.001
% 11.25/1.94  
% 11.25/1.94  ------ QBF
% 11.25/1.94  
% 11.25/1.94  qbf_q_res:                              0
% 11.25/1.94  qbf_num_tautologies:                    0
% 11.25/1.94  qbf_prep_cycles:                        0
% 11.25/1.94  
% 11.25/1.94  ------ BMC1
% 11.25/1.94  
% 11.25/1.94  bmc1_current_bound:                     -1
% 11.25/1.94  bmc1_last_solved_bound:                 -1
% 11.25/1.94  bmc1_unsat_core_size:                   -1
% 11.25/1.94  bmc1_unsat_core_parents_size:           -1
% 11.25/1.94  bmc1_merge_next_fun:                    0
% 11.25/1.94  bmc1_unsat_core_clauses_time:           0.
% 11.25/1.94  
% 11.25/1.94  ------ Instantiation
% 11.25/1.94  
% 11.25/1.94  inst_num_of_clauses:                    4594
% 11.25/1.94  inst_num_in_passive:                    2436
% 11.25/1.94  inst_num_in_active:                     1858
% 11.25/1.94  inst_num_in_unprocessed:                302
% 11.25/1.94  inst_num_of_loops:                      2760
% 11.25/1.94  inst_num_of_learning_restarts:          0
% 11.25/1.94  inst_num_moves_active_passive:          901
% 11.25/1.94  inst_lit_activity:                      0
% 11.25/1.94  inst_lit_activity_moves:                0
% 11.25/1.94  inst_num_tautologies:                   0
% 11.25/1.94  inst_num_prop_implied:                  0
% 11.25/1.94  inst_num_existing_simplified:           0
% 11.25/1.94  inst_num_eq_res_simplified:             0
% 11.25/1.94  inst_num_child_elim:                    0
% 11.25/1.94  inst_num_of_dismatching_blockings:      4510
% 11.25/1.94  inst_num_of_non_proper_insts:           6609
% 11.25/1.94  inst_num_of_duplicates:                 0
% 11.25/1.94  inst_inst_num_from_inst_to_res:         0
% 11.25/1.94  inst_dismatching_checking_time:         0.
% 11.25/1.94  
% 11.25/1.94  ------ Resolution
% 11.25/1.94  
% 11.25/1.94  res_num_of_clauses:                     0
% 11.25/1.94  res_num_in_passive:                     0
% 11.25/1.94  res_num_in_active:                      0
% 11.25/1.94  res_num_of_loops:                       223
% 11.25/1.94  res_forward_subset_subsumed:            352
% 11.25/1.94  res_backward_subset_subsumed:           4
% 11.25/1.94  res_forward_subsumed:                   0
% 11.25/1.94  res_backward_subsumed:                  0
% 11.25/1.94  res_forward_subsumption_resolution:     0
% 11.25/1.94  res_backward_subsumption_resolution:    0
% 11.25/1.94  res_clause_to_clause_subsumption:       5603
% 11.25/1.94  res_orphan_elimination:                 0
% 11.25/1.94  res_tautology_del:                      278
% 11.25/1.94  res_num_eq_res_simplified:              0
% 11.25/1.94  res_num_sel_changes:                    0
% 11.25/1.94  res_moves_from_active_to_pass:          0
% 11.25/1.94  
% 11.25/1.94  ------ Superposition
% 11.25/1.94  
% 11.25/1.94  sup_time_total:                         0.
% 11.25/1.94  sup_time_generating:                    0.
% 11.25/1.94  sup_time_sim_full:                      0.
% 11.25/1.94  sup_time_sim_immed:                     0.
% 11.25/1.94  
% 11.25/1.94  sup_num_of_clauses:                     1264
% 11.25/1.94  sup_num_in_active:                      424
% 11.25/1.94  sup_num_in_passive:                     840
% 11.25/1.94  sup_num_of_loops:                       551
% 11.25/1.94  sup_fw_superposition:                   1404
% 11.25/1.94  sup_bw_superposition:                   531
% 11.25/1.94  sup_immediate_simplified:               641
% 11.25/1.94  sup_given_eliminated:                   8
% 11.25/1.94  comparisons_done:                       0
% 11.25/1.94  comparisons_avoided:                    12
% 11.25/1.94  
% 11.25/1.94  ------ Simplifications
% 11.25/1.94  
% 11.25/1.94  
% 11.25/1.94  sim_fw_subset_subsumed:                 65
% 11.25/1.94  sim_bw_subset_subsumed:                 12
% 11.25/1.94  sim_fw_subsumed:                        264
% 11.25/1.94  sim_bw_subsumed:                        21
% 11.25/1.94  sim_fw_subsumption_res:                 0
% 11.25/1.94  sim_bw_subsumption_res:                 0
% 11.25/1.94  sim_tautology_del:                      11
% 11.25/1.94  sim_eq_tautology_del:                   165
% 11.25/1.94  sim_eq_res_simp:                        0
% 11.25/1.94  sim_fw_demodulated:                     182
% 11.25/1.94  sim_bw_demodulated:                     118
% 11.25/1.94  sim_light_normalised:                   328
% 11.25/1.94  sim_joinable_taut:                      0
% 11.25/1.94  sim_joinable_simp:                      0
% 11.25/1.94  sim_ac_normalised:                      0
% 11.25/1.94  sim_smt_subsumption:                    0
% 11.25/1.94  
%------------------------------------------------------------------------------
