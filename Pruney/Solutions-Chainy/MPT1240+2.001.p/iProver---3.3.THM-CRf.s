%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:57 EST 2020

% Result     : Theorem 43.69s
% Output     : CNFRefutation 43.69s
% Verified   : 
% Statistics : Number of formulae       :  234 (1472 expanded)
%              Number of clauses        :  128 ( 420 expanded)
%              Number of leaves         :   33 ( 344 expanded)
%              Depth                    :   26
%              Number of atoms          :  701 (10170 expanded)
%              Number of equality atoms :  191 ( 579 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f69])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f133,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
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
    inference(nnf_transformation,[],[f14])).

fof(f97,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f134,plain,(
    ! [X1] : k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1) ),
    inference(equality_resolution,[],[f97])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f131,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f89,f92])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f65,plain,(
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

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f65])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f66,f67])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f53,plain,(
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

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v2_pre_topc(X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f63,plain,(
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

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f64])).

fof(f74,plain,(
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
    inference(flattening,[],[f73])).

fof(f75,plain,(
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
    inference(rectify,[],[f74])).

fof(f78,plain,(
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

fof(f77,plain,(
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

fof(f76,plain,
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

fof(f79,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f75,f78,f77,f76])).

fof(f122,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f125,plain,
    ( v3_pre_topc(sK4,sK1)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f79])).

fof(f124,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f79])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f113,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f112,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f123,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f79])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f128,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r1_tarski(X3,sK3)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f121,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f23,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(definition_unfolding,[],[f87,f92])).

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

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f127,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f79])).

fof(f126,plain,
    ( r1_tarski(sK4,sK3)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_19,plain,
    ( r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1720,plain,
    ( r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1721,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1727,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1724,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7342,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_1724])).

cnf(c_52499,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_7342])).

cnf(c_83766,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_52499])).

cnf(c_17,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1733,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9,c_11])).

cnf(c_1734,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17,c_1733])).

cnf(c_103369,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_83766,c_1734])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1729,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_103375,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_103369,c_1729])).

cnf(c_172837,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1720,c_103375])).

cnf(c_22,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1717,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_175184,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_172837,c_1717])).

cnf(c_25,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_100,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_175192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_175184,c_100])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1712,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_175202,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_175192,c_1712])).

cnf(c_34,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_663,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_46])).

cnf(c_664,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_43,negated_conjecture,
    ( v3_pre_topc(sK4,sK1)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)
    | sK4 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_664,c_43])).

cnf(c_719,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_721,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_44])).

cnf(c_1699,plain,
    ( k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_32,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_31,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_472,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_32,c_31])).

cnf(c_604,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_472,c_46])).

cnf(c_605,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_1739,plain,
    ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1699,c_605])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1787,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1739])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_46])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_1833,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_40,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_37,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_486,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_47])).

cnf(c_487,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_46])).

cnf(c_492,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_491])).

cnf(c_752,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X0,sK3)
    | k1_tops_1(sK1,X1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_492])).

cnf(c_753,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_46])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_757,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_640])).

cnf(c_1853,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_2562,plain,
    ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1739,c_45,c_1787,c_1833,c_1853])).

cnf(c_177700,plain,
    ( k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4)) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
    inference(demodulation,[status(thm)],[c_175202,c_2562])).

cnf(c_1706,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_1735,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1706,c_605])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_1834,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(c_1854,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1853])).

cnf(c_2541,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1735,c_50,c_1834,c_1854])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1715,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5716,plain,
    ( k3_subset_1(k2_struct_0(sK1),sK4) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
    inference(superposition,[status(thm)],[c_2541,c_1715])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_46])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_1701,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_1738,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1701,c_605])).

cnf(c_2547,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
    inference(superposition,[status(thm)],[c_2541,c_1738])).

cnf(c_6254,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
    inference(demodulation,[status(thm)],[c_5716,c_2547])).

cnf(c_177775,plain,
    ( k3_subset_1(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK4)) = k1_tops_1(sK1,sK4) ),
    inference(demodulation,[status(thm)],[c_177700,c_6254])).

cnf(c_175203,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_175192,c_1715])).

cnf(c_175646,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_175203,c_1733])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1711,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2878,plain,
    ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),X0),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_1711])).

cnf(c_175565,plain,
    ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_struct_0(sK1)),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) ),
    inference(superposition,[status(thm)],[c_175192,c_2878])).

cnf(c_175648,plain,
    ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) ),
    inference(demodulation,[status(thm)],[c_175646,c_175565])).

cnf(c_29,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1710,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1713,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3731,plain,
    ( k4_subset_1(k2_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_1713])).

cnf(c_4338,plain,
    ( k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) = k2_xboole_0(k1_xboole_0,sK4) ),
    inference(superposition,[status(thm)],[c_1710,c_3731])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X0)))) = k4_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1726,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,X2)
    | r1_tarski(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7369,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1727,c_1726])).

cnf(c_7376,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_7369,c_11,c_1733])).

cnf(c_7473,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_7376])).

cnf(c_7483,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7473,c_11])).

cnf(c_7494,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_7483])).

cnf(c_9517,plain,
    ( k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_4338,c_7494])).

cnf(c_175652,plain,
    ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_175648,c_9517])).

cnf(c_175653,plain,
    ( k3_subset_1(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_175202,c_175652])).

cnf(c_177776,plain,
    ( k1_tops_1(sK1,sK4) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_177775,c_175653])).

cnf(c_1107,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1884,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1107])).

cnf(c_3134,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,sK4)
    | X0 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1884])).

cnf(c_7562,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | ~ r2_hidden(sK2,sK4)
    | k1_tops_1(sK1,sK4) != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3134])).

cnf(c_1881,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2288,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X0,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1881])).

cnf(c_2621,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2288])).

cnf(c_2909,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2621])).

cnf(c_1103,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2859,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_46])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_1953,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK3)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_2170,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3))
    | ~ r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1953])).

cnf(c_41,negated_conjecture,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_42,negated_conjecture,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f126])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_177776,c_7562,c_2909,c_2859,c_2170,c_1853,c_1833,c_41,c_42,c_44,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:14:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.69/5.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.69/5.99  
% 43.69/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.69/5.99  
% 43.69/5.99  ------  iProver source info
% 43.69/5.99  
% 43.69/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.69/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.69/5.99  git: non_committed_changes: false
% 43.69/5.99  git: last_make_outside_of_git: false
% 43.69/5.99  
% 43.69/5.99  ------ 
% 43.69/5.99  
% 43.69/5.99  ------ Input Options
% 43.69/5.99  
% 43.69/5.99  --out_options                           all
% 43.69/5.99  --tptp_safe_out                         true
% 43.69/5.99  --problem_path                          ""
% 43.69/5.99  --include_path                          ""
% 43.69/5.99  --clausifier                            res/vclausify_rel
% 43.69/5.99  --clausifier_options                    ""
% 43.69/5.99  --stdin                                 false
% 43.69/5.99  --stats_out                             all
% 43.69/5.99  
% 43.69/5.99  ------ General Options
% 43.69/5.99  
% 43.69/5.99  --fof                                   false
% 43.69/5.99  --time_out_real                         305.
% 43.69/5.99  --time_out_virtual                      -1.
% 43.69/5.99  --symbol_type_check                     false
% 43.69/5.99  --clausify_out                          false
% 43.69/5.99  --sig_cnt_out                           false
% 43.69/5.99  --trig_cnt_out                          false
% 43.69/5.99  --trig_cnt_out_tolerance                1.
% 43.69/5.99  --trig_cnt_out_sk_spl                   false
% 43.69/5.99  --abstr_cl_out                          false
% 43.69/5.99  
% 43.69/5.99  ------ Global Options
% 43.69/5.99  
% 43.69/5.99  --schedule                              default
% 43.69/5.99  --add_important_lit                     false
% 43.69/5.99  --prop_solver_per_cl                    1000
% 43.69/5.99  --min_unsat_core                        false
% 43.69/5.99  --soft_assumptions                      false
% 43.69/5.99  --soft_lemma_size                       3
% 43.69/5.99  --prop_impl_unit_size                   0
% 43.69/5.99  --prop_impl_unit                        []
% 43.69/5.99  --share_sel_clauses                     true
% 43.69/5.99  --reset_solvers                         false
% 43.69/5.99  --bc_imp_inh                            [conj_cone]
% 43.69/5.99  --conj_cone_tolerance                   3.
% 43.69/5.99  --extra_neg_conj                        none
% 43.69/5.99  --large_theory_mode                     true
% 43.69/5.99  --prolific_symb_bound                   200
% 43.69/5.99  --lt_threshold                          2000
% 43.69/5.99  --clause_weak_htbl                      true
% 43.69/5.99  --gc_record_bc_elim                     false
% 43.69/5.99  
% 43.69/5.99  ------ Preprocessing Options
% 43.69/5.99  
% 43.69/5.99  --preprocessing_flag                    true
% 43.69/5.99  --time_out_prep_mult                    0.1
% 43.69/5.99  --splitting_mode                        input
% 43.69/5.99  --splitting_grd                         true
% 43.69/5.99  --splitting_cvd                         false
% 43.69/5.99  --splitting_cvd_svl                     false
% 43.69/5.99  --splitting_nvd                         32
% 43.69/5.99  --sub_typing                            true
% 43.69/5.99  --prep_gs_sim                           true
% 43.69/5.99  --prep_unflatten                        true
% 43.69/5.99  --prep_res_sim                          true
% 43.69/5.99  --prep_upred                            true
% 43.69/5.99  --prep_sem_filter                       exhaustive
% 43.69/5.99  --prep_sem_filter_out                   false
% 43.69/5.99  --pred_elim                             true
% 43.69/5.99  --res_sim_input                         true
% 43.69/5.99  --eq_ax_congr_red                       true
% 43.69/5.99  --pure_diseq_elim                       true
% 43.69/5.99  --brand_transform                       false
% 43.69/5.99  --non_eq_to_eq                          false
% 43.69/5.99  --prep_def_merge                        true
% 43.69/5.99  --prep_def_merge_prop_impl              false
% 43.69/5.99  --prep_def_merge_mbd                    true
% 43.69/5.99  --prep_def_merge_tr_red                 false
% 43.69/5.99  --prep_def_merge_tr_cl                  false
% 43.69/5.99  --smt_preprocessing                     true
% 43.69/5.99  --smt_ac_axioms                         fast
% 43.69/5.99  --preprocessed_out                      false
% 43.69/5.99  --preprocessed_stats                    false
% 43.69/5.99  
% 43.69/5.99  ------ Abstraction refinement Options
% 43.69/5.99  
% 43.69/5.99  --abstr_ref                             []
% 43.69/5.99  --abstr_ref_prep                        false
% 43.69/5.99  --abstr_ref_until_sat                   false
% 43.69/5.99  --abstr_ref_sig_restrict                funpre
% 43.69/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 43.69/5.99  --abstr_ref_under                       []
% 43.69/5.99  
% 43.69/5.99  ------ SAT Options
% 43.69/5.99  
% 43.69/5.99  --sat_mode                              false
% 43.69/5.99  --sat_fm_restart_options                ""
% 43.69/5.99  --sat_gr_def                            false
% 43.69/5.99  --sat_epr_types                         true
% 43.69/5.99  --sat_non_cyclic_types                  false
% 43.69/5.99  --sat_finite_models                     false
% 43.69/5.99  --sat_fm_lemmas                         false
% 43.69/5.99  --sat_fm_prep                           false
% 43.69/5.99  --sat_fm_uc_incr                        true
% 43.69/5.99  --sat_out_model                         small
% 43.69/5.99  --sat_out_clauses                       false
% 43.69/5.99  
% 43.69/5.99  ------ QBF Options
% 43.69/5.99  
% 43.69/5.99  --qbf_mode                              false
% 43.69/5.99  --qbf_elim_univ                         false
% 43.69/5.99  --qbf_dom_inst                          none
% 43.69/5.99  --qbf_dom_pre_inst                      false
% 43.69/5.99  --qbf_sk_in                             false
% 43.69/5.99  --qbf_pred_elim                         true
% 43.69/5.99  --qbf_split                             512
% 43.69/5.99  
% 43.69/5.99  ------ BMC1 Options
% 43.69/5.99  
% 43.69/5.99  --bmc1_incremental                      false
% 43.69/5.99  --bmc1_axioms                           reachable_all
% 43.69/5.99  --bmc1_min_bound                        0
% 43.69/5.99  --bmc1_max_bound                        -1
% 43.69/5.99  --bmc1_max_bound_default                -1
% 43.69/5.99  --bmc1_symbol_reachability              true
% 43.69/5.99  --bmc1_property_lemmas                  false
% 43.69/5.99  --bmc1_k_induction                      false
% 43.69/5.99  --bmc1_non_equiv_states                 false
% 43.69/5.99  --bmc1_deadlock                         false
% 43.69/5.99  --bmc1_ucm                              false
% 43.69/5.99  --bmc1_add_unsat_core                   none
% 43.69/5.99  --bmc1_unsat_core_children              false
% 43.69/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 43.69/5.99  --bmc1_out_stat                         full
% 43.69/5.99  --bmc1_ground_init                      false
% 43.69/5.99  --bmc1_pre_inst_next_state              false
% 43.69/5.99  --bmc1_pre_inst_state                   false
% 43.69/5.99  --bmc1_pre_inst_reach_state             false
% 43.69/5.99  --bmc1_out_unsat_core                   false
% 43.69/5.99  --bmc1_aig_witness_out                  false
% 43.69/5.99  --bmc1_verbose                          false
% 43.69/5.99  --bmc1_dump_clauses_tptp                false
% 43.69/5.99  --bmc1_dump_unsat_core_tptp             false
% 43.69/5.99  --bmc1_dump_file                        -
% 43.69/5.99  --bmc1_ucm_expand_uc_limit              128
% 43.69/5.99  --bmc1_ucm_n_expand_iterations          6
% 43.69/5.99  --bmc1_ucm_extend_mode                  1
% 43.69/5.99  --bmc1_ucm_init_mode                    2
% 43.69/5.99  --bmc1_ucm_cone_mode                    none
% 43.69/5.99  --bmc1_ucm_reduced_relation_type        0
% 43.69/5.99  --bmc1_ucm_relax_model                  4
% 43.69/5.99  --bmc1_ucm_full_tr_after_sat            true
% 43.69/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 43.69/5.99  --bmc1_ucm_layered_model                none
% 43.69/5.99  --bmc1_ucm_max_lemma_size               10
% 43.69/5.99  
% 43.69/5.99  ------ AIG Options
% 43.69/5.99  
% 43.69/5.99  --aig_mode                              false
% 43.69/5.99  
% 43.69/5.99  ------ Instantiation Options
% 43.69/5.99  
% 43.69/5.99  --instantiation_flag                    true
% 43.69/5.99  --inst_sos_flag                         true
% 43.69/5.99  --inst_sos_phase                        true
% 43.69/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.69/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.69/5.99  --inst_lit_sel_side                     num_symb
% 43.69/5.99  --inst_solver_per_active                1400
% 43.69/5.99  --inst_solver_calls_frac                1.
% 43.69/5.99  --inst_passive_queue_type               priority_queues
% 43.69/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.69/5.99  --inst_passive_queues_freq              [25;2]
% 43.69/5.99  --inst_dismatching                      true
% 43.69/5.99  --inst_eager_unprocessed_to_passive     true
% 43.69/5.99  --inst_prop_sim_given                   true
% 43.69/5.99  --inst_prop_sim_new                     false
% 43.69/5.99  --inst_subs_new                         false
% 43.69/5.99  --inst_eq_res_simp                      false
% 43.69/5.99  --inst_subs_given                       false
% 43.69/5.99  --inst_orphan_elimination               true
% 43.69/5.99  --inst_learning_loop_flag               true
% 43.69/5.99  --inst_learning_start                   3000
% 43.69/5.99  --inst_learning_factor                  2
% 43.69/5.99  --inst_start_prop_sim_after_learn       3
% 43.69/5.99  --inst_sel_renew                        solver
% 43.69/5.99  --inst_lit_activity_flag                true
% 43.69/5.99  --inst_restr_to_given                   false
% 43.69/5.99  --inst_activity_threshold               500
% 43.69/5.99  --inst_out_proof                        true
% 43.69/5.99  
% 43.69/5.99  ------ Resolution Options
% 43.69/5.99  
% 43.69/5.99  --resolution_flag                       true
% 43.69/5.99  --res_lit_sel                           adaptive
% 43.69/5.99  --res_lit_sel_side                      none
% 43.69/5.99  --res_ordering                          kbo
% 43.69/5.99  --res_to_prop_solver                    active
% 43.69/5.99  --res_prop_simpl_new                    false
% 43.69/5.99  --res_prop_simpl_given                  true
% 43.69/5.99  --res_passive_queue_type                priority_queues
% 43.69/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.69/5.99  --res_passive_queues_freq               [15;5]
% 43.69/5.99  --res_forward_subs                      full
% 43.69/5.99  --res_backward_subs                     full
% 43.69/5.99  --res_forward_subs_resolution           true
% 43.69/5.99  --res_backward_subs_resolution          true
% 43.69/5.99  --res_orphan_elimination                true
% 43.69/5.99  --res_time_limit                        2.
% 43.69/5.99  --res_out_proof                         true
% 43.69/5.99  
% 43.69/5.99  ------ Superposition Options
% 43.69/5.99  
% 43.69/5.99  --superposition_flag                    true
% 43.69/5.99  --sup_passive_queue_type                priority_queues
% 43.69/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.69/5.99  --sup_passive_queues_freq               [8;1;4]
% 43.69/5.99  --demod_completeness_check              fast
% 43.69/5.99  --demod_use_ground                      true
% 43.69/5.99  --sup_to_prop_solver                    passive
% 43.69/5.99  --sup_prop_simpl_new                    true
% 43.69/5.99  --sup_prop_simpl_given                  true
% 43.69/5.99  --sup_fun_splitting                     true
% 43.69/5.99  --sup_smt_interval                      50000
% 43.69/5.99  
% 43.69/5.99  ------ Superposition Simplification Setup
% 43.69/5.99  
% 43.69/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.69/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.69/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.69/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.69/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 43.69/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.69/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.69/5.99  --sup_immed_triv                        [TrivRules]
% 43.69/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.69/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.69/5.99  --sup_immed_bw_main                     []
% 43.69/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.69/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 43.69/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.69/5.99  --sup_input_bw                          []
% 43.69/5.99  
% 43.69/5.99  ------ Combination Options
% 43.69/5.99  
% 43.69/5.99  --comb_res_mult                         3
% 43.69/5.99  --comb_sup_mult                         2
% 43.69/5.99  --comb_inst_mult                        10
% 43.69/5.99  
% 43.69/5.99  ------ Debug Options
% 43.69/5.99  
% 43.69/5.99  --dbg_backtrace                         false
% 43.69/5.99  --dbg_dump_prop_clauses                 false
% 43.69/5.99  --dbg_dump_prop_clauses_file            -
% 43.69/5.99  --dbg_out_stat                          false
% 43.69/5.99  ------ Parsing...
% 43.69/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.69/5.99  
% 43.69/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 43.69/5.99  
% 43.69/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.69/5.99  
% 43.69/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.69/5.99  ------ Proving...
% 43.69/5.99  ------ Problem Properties 
% 43.69/5.99  
% 43.69/5.99  
% 43.69/5.99  clauses                                 43
% 43.69/5.99  conjectures                             4
% 43.69/5.99  EPR                                     8
% 43.69/5.99  Horn                                    34
% 43.69/5.99  unary                                   12
% 43.69/5.99  binary                                  18
% 43.69/5.99  lits                                    92
% 43.69/5.99  lits eq                                 22
% 43.69/5.99  fd_pure                                 0
% 43.69/5.99  fd_pseudo                               0
% 43.69/5.99  fd_cond                                 1
% 43.69/5.99  fd_pseudo_cond                          2
% 43.69/5.99  AC symbols                              0
% 43.69/5.99  
% 43.69/5.99  ------ Schedule dynamic 5 is on 
% 43.69/5.99  
% 43.69/5.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.69/5.99  
% 43.69/5.99  
% 43.69/5.99  ------ 
% 43.69/5.99  Current options:
% 43.69/5.99  ------ 
% 43.69/5.99  
% 43.69/5.99  ------ Input Options
% 43.69/5.99  
% 43.69/5.99  --out_options                           all
% 43.69/5.99  --tptp_safe_out                         true
% 43.69/5.99  --problem_path                          ""
% 43.69/5.99  --include_path                          ""
% 43.69/5.99  --clausifier                            res/vclausify_rel
% 43.69/5.99  --clausifier_options                    ""
% 43.69/5.99  --stdin                                 false
% 43.69/5.99  --stats_out                             all
% 43.69/5.99  
% 43.69/5.99  ------ General Options
% 43.69/5.99  
% 43.69/5.99  --fof                                   false
% 43.69/5.99  --time_out_real                         305.
% 43.69/5.99  --time_out_virtual                      -1.
% 43.69/5.99  --symbol_type_check                     false
% 43.69/5.99  --clausify_out                          false
% 43.69/5.99  --sig_cnt_out                           false
% 43.69/5.99  --trig_cnt_out                          false
% 43.69/5.99  --trig_cnt_out_tolerance                1.
% 43.69/5.99  --trig_cnt_out_sk_spl                   false
% 43.69/5.99  --abstr_cl_out                          false
% 43.69/5.99  
% 43.69/5.99  ------ Global Options
% 43.69/5.99  
% 43.69/5.99  --schedule                              default
% 43.69/5.99  --add_important_lit                     false
% 43.69/5.99  --prop_solver_per_cl                    1000
% 43.69/5.99  --min_unsat_core                        false
% 43.69/5.99  --soft_assumptions                      false
% 43.69/5.99  --soft_lemma_size                       3
% 43.69/5.99  --prop_impl_unit_size                   0
% 43.69/5.99  --prop_impl_unit                        []
% 43.69/5.99  --share_sel_clauses                     true
% 43.69/5.99  --reset_solvers                         false
% 43.69/5.99  --bc_imp_inh                            [conj_cone]
% 43.69/5.99  --conj_cone_tolerance                   3.
% 43.69/5.99  --extra_neg_conj                        none
% 43.69/5.99  --large_theory_mode                     true
% 43.69/5.99  --prolific_symb_bound                   200
% 43.69/5.99  --lt_threshold                          2000
% 43.69/5.99  --clause_weak_htbl                      true
% 43.69/5.99  --gc_record_bc_elim                     false
% 43.69/5.99  
% 43.69/5.99  ------ Preprocessing Options
% 43.69/5.99  
% 43.69/5.99  --preprocessing_flag                    true
% 43.69/5.99  --time_out_prep_mult                    0.1
% 43.69/5.99  --splitting_mode                        input
% 43.69/5.99  --splitting_grd                         true
% 43.69/5.99  --splitting_cvd                         false
% 43.69/5.99  --splitting_cvd_svl                     false
% 43.69/5.99  --splitting_nvd                         32
% 43.69/5.99  --sub_typing                            true
% 43.69/5.99  --prep_gs_sim                           true
% 43.69/5.99  --prep_unflatten                        true
% 43.69/5.99  --prep_res_sim                          true
% 43.69/5.99  --prep_upred                            true
% 43.69/5.99  --prep_sem_filter                       exhaustive
% 43.69/5.99  --prep_sem_filter_out                   false
% 43.69/5.99  --pred_elim                             true
% 43.69/5.99  --res_sim_input                         true
% 43.69/5.99  --eq_ax_congr_red                       true
% 43.69/5.99  --pure_diseq_elim                       true
% 43.69/5.99  --brand_transform                       false
% 43.69/5.99  --non_eq_to_eq                          false
% 43.69/5.99  --prep_def_merge                        true
% 43.69/5.99  --prep_def_merge_prop_impl              false
% 43.69/5.99  --prep_def_merge_mbd                    true
% 43.69/5.99  --prep_def_merge_tr_red                 false
% 43.69/5.99  --prep_def_merge_tr_cl                  false
% 43.69/5.99  --smt_preprocessing                     true
% 43.69/5.99  --smt_ac_axioms                         fast
% 43.69/5.99  --preprocessed_out                      false
% 43.69/5.99  --preprocessed_stats                    false
% 43.69/5.99  
% 43.69/5.99  ------ Abstraction refinement Options
% 43.69/5.99  
% 43.69/5.99  --abstr_ref                             []
% 43.69/5.99  --abstr_ref_prep                        false
% 43.69/5.99  --abstr_ref_until_sat                   false
% 43.69/5.99  --abstr_ref_sig_restrict                funpre
% 43.69/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 43.69/5.99  --abstr_ref_under                       []
% 43.69/5.99  
% 43.69/5.99  ------ SAT Options
% 43.69/5.99  
% 43.69/5.99  --sat_mode                              false
% 43.69/5.99  --sat_fm_restart_options                ""
% 43.69/5.99  --sat_gr_def                            false
% 43.69/5.99  --sat_epr_types                         true
% 43.69/5.99  --sat_non_cyclic_types                  false
% 43.69/5.99  --sat_finite_models                     false
% 43.69/5.99  --sat_fm_lemmas                         false
% 43.69/5.99  --sat_fm_prep                           false
% 43.69/5.99  --sat_fm_uc_incr                        true
% 43.69/5.99  --sat_out_model                         small
% 43.69/5.99  --sat_out_clauses                       false
% 43.69/5.99  
% 43.69/5.99  ------ QBF Options
% 43.69/5.99  
% 43.69/5.99  --qbf_mode                              false
% 43.69/5.99  --qbf_elim_univ                         false
% 43.69/5.99  --qbf_dom_inst                          none
% 43.69/5.99  --qbf_dom_pre_inst                      false
% 43.69/5.99  --qbf_sk_in                             false
% 43.69/5.99  --qbf_pred_elim                         true
% 43.69/5.99  --qbf_split                             512
% 43.69/5.99  
% 43.69/5.99  ------ BMC1 Options
% 43.69/5.99  
% 43.69/5.99  --bmc1_incremental                      false
% 43.69/5.99  --bmc1_axioms                           reachable_all
% 43.69/5.99  --bmc1_min_bound                        0
% 43.69/5.99  --bmc1_max_bound                        -1
% 43.69/5.99  --bmc1_max_bound_default                -1
% 43.69/5.99  --bmc1_symbol_reachability              true
% 43.69/5.99  --bmc1_property_lemmas                  false
% 43.69/5.99  --bmc1_k_induction                      false
% 43.69/5.99  --bmc1_non_equiv_states                 false
% 43.69/5.99  --bmc1_deadlock                         false
% 43.69/5.99  --bmc1_ucm                              false
% 43.69/5.99  --bmc1_add_unsat_core                   none
% 43.69/5.99  --bmc1_unsat_core_children              false
% 43.69/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 43.69/5.99  --bmc1_out_stat                         full
% 43.69/5.99  --bmc1_ground_init                      false
% 43.69/5.99  --bmc1_pre_inst_next_state              false
% 43.69/5.99  --bmc1_pre_inst_state                   false
% 43.69/5.99  --bmc1_pre_inst_reach_state             false
% 43.69/5.99  --bmc1_out_unsat_core                   false
% 43.69/5.99  --bmc1_aig_witness_out                  false
% 43.69/5.99  --bmc1_verbose                          false
% 43.69/5.99  --bmc1_dump_clauses_tptp                false
% 43.69/5.99  --bmc1_dump_unsat_core_tptp             false
% 43.69/5.99  --bmc1_dump_file                        -
% 43.69/5.99  --bmc1_ucm_expand_uc_limit              128
% 43.69/5.99  --bmc1_ucm_n_expand_iterations          6
% 43.69/5.99  --bmc1_ucm_extend_mode                  1
% 43.69/5.99  --bmc1_ucm_init_mode                    2
% 43.69/5.99  --bmc1_ucm_cone_mode                    none
% 43.69/5.99  --bmc1_ucm_reduced_relation_type        0
% 43.69/5.99  --bmc1_ucm_relax_model                  4
% 43.69/5.99  --bmc1_ucm_full_tr_after_sat            true
% 43.69/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 43.69/5.99  --bmc1_ucm_layered_model                none
% 43.69/5.99  --bmc1_ucm_max_lemma_size               10
% 43.69/5.99  
% 43.69/5.99  ------ AIG Options
% 43.69/5.99  
% 43.69/5.99  --aig_mode                              false
% 43.69/5.99  
% 43.69/5.99  ------ Instantiation Options
% 43.69/5.99  
% 43.69/5.99  --instantiation_flag                    true
% 43.69/5.99  --inst_sos_flag                         true
% 43.69/5.99  --inst_sos_phase                        true
% 43.69/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.69/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.69/5.99  --inst_lit_sel_side                     none
% 43.69/5.99  --inst_solver_per_active                1400
% 43.69/5.99  --inst_solver_calls_frac                1.
% 43.69/5.99  --inst_passive_queue_type               priority_queues
% 43.69/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.69/5.99  --inst_passive_queues_freq              [25;2]
% 43.69/5.99  --inst_dismatching                      true
% 43.69/5.99  --inst_eager_unprocessed_to_passive     true
% 43.69/5.99  --inst_prop_sim_given                   true
% 43.69/5.99  --inst_prop_sim_new                     false
% 43.69/5.99  --inst_subs_new                         false
% 43.69/5.99  --inst_eq_res_simp                      false
% 43.69/5.99  --inst_subs_given                       false
% 43.69/5.99  --inst_orphan_elimination               true
% 43.69/5.99  --inst_learning_loop_flag               true
% 43.69/5.99  --inst_learning_start                   3000
% 43.69/5.99  --inst_learning_factor                  2
% 43.69/5.99  --inst_start_prop_sim_after_learn       3
% 43.69/5.99  --inst_sel_renew                        solver
% 43.69/5.99  --inst_lit_activity_flag                true
% 43.69/5.99  --inst_restr_to_given                   false
% 43.69/5.99  --inst_activity_threshold               500
% 43.69/5.99  --inst_out_proof                        true
% 43.69/5.99  
% 43.69/5.99  ------ Resolution Options
% 43.69/5.99  
% 43.69/5.99  --resolution_flag                       false
% 43.69/5.99  --res_lit_sel                           adaptive
% 43.69/5.99  --res_lit_sel_side                      none
% 43.69/5.99  --res_ordering                          kbo
% 43.69/5.99  --res_to_prop_solver                    active
% 43.69/5.99  --res_prop_simpl_new                    false
% 43.69/5.99  --res_prop_simpl_given                  true
% 43.69/5.99  --res_passive_queue_type                priority_queues
% 43.69/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.69/5.99  --res_passive_queues_freq               [15;5]
% 43.69/5.99  --res_forward_subs                      full
% 43.69/5.99  --res_backward_subs                     full
% 43.69/5.99  --res_forward_subs_resolution           true
% 43.69/5.99  --res_backward_subs_resolution          true
% 43.69/5.99  --res_orphan_elimination                true
% 43.69/5.99  --res_time_limit                        2.
% 43.69/5.99  --res_out_proof                         true
% 43.69/5.99  
% 43.69/5.99  ------ Superposition Options
% 43.69/5.99  
% 43.69/5.99  --superposition_flag                    true
% 43.69/5.99  --sup_passive_queue_type                priority_queues
% 43.69/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.69/5.99  --sup_passive_queues_freq               [8;1;4]
% 43.69/5.99  --demod_completeness_check              fast
% 43.69/5.99  --demod_use_ground                      true
% 43.69/5.99  --sup_to_prop_solver                    passive
% 43.69/5.99  --sup_prop_simpl_new                    true
% 43.69/5.99  --sup_prop_simpl_given                  true
% 43.69/5.99  --sup_fun_splitting                     true
% 43.69/5.99  --sup_smt_interval                      50000
% 43.69/5.99  
% 43.69/5.99  ------ Superposition Simplification Setup
% 43.69/5.99  
% 43.69/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.69/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.69/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.69/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.69/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 43.69/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.69/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.69/5.99  --sup_immed_triv                        [TrivRules]
% 43.69/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.69/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.69/5.99  --sup_immed_bw_main                     []
% 43.69/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.69/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 43.69/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.69/5.99  --sup_input_bw                          []
% 43.69/5.99  
% 43.69/5.99  ------ Combination Options
% 43.69/5.99  
% 43.69/5.99  --comb_res_mult                         3
% 43.69/5.99  --comb_sup_mult                         2
% 43.69/5.99  --comb_inst_mult                        10
% 43.69/5.99  
% 43.69/5.99  ------ Debug Options
% 43.69/5.99  
% 43.69/5.99  --dbg_backtrace                         false
% 43.69/5.99  --dbg_dump_prop_clauses                 false
% 43.69/5.99  --dbg_dump_prop_clauses_file            -
% 43.69/5.99  --dbg_out_stat                          false
% 43.69/5.99  
% 43.69/5.99  
% 43.69/5.99  
% 43.69/5.99  
% 43.69/5.99  ------ Proving...
% 43.69/5.99  
% 43.69/5.99  
% 43.69/5.99  % SZS status Theorem for theBenchmark.p
% 43.69/5.99  
% 43.69/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 43.69/5.99  
% 43.69/5.99  fof(f16,axiom,(
% 43.69/5.99    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f100,plain,(
% 43.69/5.99    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 43.69/5.99    inference(cnf_transformation,[],[f16])).
% 43.69/5.99  
% 43.69/5.99  fof(f15,axiom,(
% 43.69/5.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f42,plain,(
% 43.69/5.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 43.69/5.99    inference(ennf_transformation,[],[f15])).
% 43.69/5.99  
% 43.69/5.99  fof(f99,plain,(
% 43.69/5.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f42])).
% 43.69/5.99  
% 43.69/5.99  fof(f3,axiom,(
% 43.69/5.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f69,plain,(
% 43.69/5.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.69/5.99    inference(nnf_transformation,[],[f3])).
% 43.69/5.99  
% 43.69/5.99  fof(f70,plain,(
% 43.69/5.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.69/5.99    inference(flattening,[],[f69])).
% 43.69/5.99  
% 43.69/5.99  fof(f84,plain,(
% 43.69/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 43.69/5.99    inference(cnf_transformation,[],[f70])).
% 43.69/5.99  
% 43.69/5.99  fof(f133,plain,(
% 43.69/5.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 43.69/5.99    inference(equality_resolution,[],[f84])).
% 43.69/5.99  
% 43.69/5.99  fof(f11,axiom,(
% 43.69/5.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f38,plain,(
% 43.69/5.99    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 43.69/5.99    inference(ennf_transformation,[],[f11])).
% 43.69/5.99  
% 43.69/5.99  fof(f39,plain,(
% 43.69/5.99    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 43.69/5.99    inference(flattening,[],[f38])).
% 43.69/5.99  
% 43.69/5.99  fof(f94,plain,(
% 43.69/5.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f39])).
% 43.69/5.99  
% 43.69/5.99  fof(f14,axiom,(
% 43.69/5.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f71,plain,(
% 43.69/5.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 43.69/5.99    inference(nnf_transformation,[],[f14])).
% 43.69/5.99  
% 43.69/5.99  fof(f97,plain,(
% 43.69/5.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f71])).
% 43.69/5.99  
% 43.69/5.99  fof(f134,plain,(
% 43.69/5.99    ( ! [X1] : (k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1)) )),
% 43.69/5.99    inference(equality_resolution,[],[f97])).
% 43.69/5.99  
% 43.69/5.99  fof(f6,axiom,(
% 43.69/5.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f89,plain,(
% 43.69/5.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 43.69/5.99    inference(cnf_transformation,[],[f6])).
% 43.69/5.99  
% 43.69/5.99  fof(f9,axiom,(
% 43.69/5.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f92,plain,(
% 43.69/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f9])).
% 43.69/5.99  
% 43.69/5.99  fof(f131,plain,(
% 43.69/5.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 43.69/5.99    inference(definition_unfolding,[],[f89,f92])).
% 43.69/5.99  
% 43.69/5.99  fof(f8,axiom,(
% 43.69/5.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f91,plain,(
% 43.69/5.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 43.69/5.99    inference(cnf_transformation,[],[f8])).
% 43.69/5.99  
% 43.69/5.99  fof(f2,axiom,(
% 43.69/5.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f35,plain,(
% 43.69/5.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 43.69/5.99    inference(ennf_transformation,[],[f2])).
% 43.69/5.99  
% 43.69/5.99  fof(f65,plain,(
% 43.69/5.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 43.69/5.99    inference(nnf_transformation,[],[f35])).
% 43.69/5.99  
% 43.69/5.99  fof(f66,plain,(
% 43.69/5.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 43.69/5.99    inference(rectify,[],[f65])).
% 43.69/5.99  
% 43.69/5.99  fof(f67,plain,(
% 43.69/5.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 43.69/5.99    introduced(choice_axiom,[])).
% 43.69/5.99  
% 43.69/5.99  fof(f68,plain,(
% 43.69/5.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 43.69/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f66,f67])).
% 43.69/5.99  
% 43.69/5.99  fof(f81,plain,(
% 43.69/5.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f68])).
% 43.69/5.99  
% 43.69/5.99  fof(f17,axiom,(
% 43.69/5.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f43,plain,(
% 43.69/5.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 43.69/5.99    inference(ennf_transformation,[],[f17])).
% 43.69/5.99  
% 43.69/5.99  fof(f72,plain,(
% 43.69/5.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 43.69/5.99    inference(nnf_transformation,[],[f43])).
% 43.69/5.99  
% 43.69/5.99  fof(f102,plain,(
% 43.69/5.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f72])).
% 43.69/5.99  
% 43.69/5.99  fof(f19,axiom,(
% 43.69/5.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f106,plain,(
% 43.69/5.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 43.69/5.99    inference(cnf_transformation,[],[f19])).
% 43.69/5.99  
% 43.69/5.99  fof(f21,axiom,(
% 43.69/5.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f47,plain,(
% 43.69/5.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.69/5.99    inference(ennf_transformation,[],[f21])).
% 43.69/5.99  
% 43.69/5.99  fof(f108,plain,(
% 43.69/5.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.69/5.99    inference(cnf_transformation,[],[f47])).
% 43.69/5.99  
% 43.69/5.99  fof(f27,axiom,(
% 43.69/5.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f53,plain,(
% 43.69/5.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0))) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.69/5.99    inference(ennf_transformation,[],[f27])).
% 43.69/5.99  
% 43.69/5.99  fof(f54,plain,(
% 43.69/5.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0)) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.69/5.99    inference(flattening,[],[f53])).
% 43.69/5.99  
% 43.69/5.99  fof(f114,plain,(
% 43.69/5.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f54])).
% 43.69/5.99  
% 43.69/5.99  fof(f33,conjecture,(
% 43.69/5.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f34,negated_conjecture,(
% 43.69/5.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 43.69/5.99    inference(negated_conjecture,[],[f33])).
% 43.69/5.99  
% 43.69/5.99  fof(f63,plain,(
% 43.69/5.99    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 43.69/5.99    inference(ennf_transformation,[],[f34])).
% 43.69/5.99  
% 43.69/5.99  fof(f64,plain,(
% 43.69/5.99    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 43.69/5.99    inference(flattening,[],[f63])).
% 43.69/5.99  
% 43.69/5.99  fof(f73,plain,(
% 43.69/5.99    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 43.69/5.99    inference(nnf_transformation,[],[f64])).
% 43.69/5.99  
% 43.69/5.99  fof(f74,plain,(
% 43.69/5.99    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 43.69/5.99    inference(flattening,[],[f73])).
% 43.69/5.99  
% 43.69/5.99  fof(f75,plain,(
% 43.69/5.99    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 43.69/5.99    inference(rectify,[],[f74])).
% 43.69/5.99  
% 43.69/5.99  fof(f78,plain,(
% 43.69/5.99    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK4) & r1_tarski(sK4,X2) & v3_pre_topc(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 43.69/5.99    introduced(choice_axiom,[])).
% 43.69/5.99  
% 43.69/5.99  fof(f77,plain,(
% 43.69/5.99    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK2,k1_tops_1(X0,sK3))) & (? [X4] : (r2_hidden(sK2,X4) & r1_tarski(X4,sK3) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK2,k1_tops_1(X0,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 43.69/5.99    introduced(choice_axiom,[])).
% 43.69/5.99  
% 43.69/5.99  fof(f76,plain,(
% 43.69/5.99    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X1,k1_tops_1(sK1,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(X1,k1_tops_1(sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 43.69/5.99    introduced(choice_axiom,[])).
% 43.69/5.99  
% 43.69/5.99  fof(f79,plain,(
% 43.69/5.99    ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(sK2,k1_tops_1(sK1,sK3))) & ((r2_hidden(sK2,sK4) & r1_tarski(sK4,sK3) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(sK2,k1_tops_1(sK1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 43.69/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f75,f78,f77,f76])).
% 43.69/5.99  
% 43.69/5.99  fof(f122,plain,(
% 43.69/5.99    l1_pre_topc(sK1)),
% 43.69/5.99    inference(cnf_transformation,[],[f79])).
% 43.69/5.99  
% 43.69/5.99  fof(f125,plain,(
% 43.69/5.99    v3_pre_topc(sK4,sK1) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 43.69/5.99    inference(cnf_transformation,[],[f79])).
% 43.69/5.99  
% 43.69/5.99  fof(f124,plain,(
% 43.69/5.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 43.69/5.99    inference(cnf_transformation,[],[f79])).
% 43.69/5.99  
% 43.69/5.99  fof(f26,axiom,(
% 43.69/5.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f52,plain,(
% 43.69/5.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 43.69/5.99    inference(ennf_transformation,[],[f26])).
% 43.69/5.99  
% 43.69/5.99  fof(f113,plain,(
% 43.69/5.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f52])).
% 43.69/5.99  
% 43.69/5.99  fof(f25,axiom,(
% 43.69/5.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f51,plain,(
% 43.69/5.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 43.69/5.99    inference(ennf_transformation,[],[f25])).
% 43.69/5.99  
% 43.69/5.99  fof(f112,plain,(
% 43.69/5.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f51])).
% 43.69/5.99  
% 43.69/5.99  fof(f123,plain,(
% 43.69/5.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 43.69/5.99    inference(cnf_transformation,[],[f79])).
% 43.69/5.99  
% 43.69/5.99  fof(f31,axiom,(
% 43.69/5.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f60,plain,(
% 43.69/5.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.69/5.99    inference(ennf_transformation,[],[f31])).
% 43.69/5.99  
% 43.69/5.99  fof(f119,plain,(
% 43.69/5.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f60])).
% 43.69/5.99  
% 43.69/5.99  fof(f128,plain,(
% 43.69/5.99    ( ! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK2,k1_tops_1(sK1,sK3))) )),
% 43.69/5.99    inference(cnf_transformation,[],[f79])).
% 43.69/5.99  
% 43.69/5.99  fof(f30,axiom,(
% 43.69/5.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f58,plain,(
% 43.69/5.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 43.69/5.99    inference(ennf_transformation,[],[f30])).
% 43.69/5.99  
% 43.69/5.99  fof(f59,plain,(
% 43.69/5.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 43.69/5.99    inference(flattening,[],[f58])).
% 43.69/5.99  
% 43.69/5.99  fof(f118,plain,(
% 43.69/5.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f59])).
% 43.69/5.99  
% 43.69/5.99  fof(f121,plain,(
% 43.69/5.99    v2_pre_topc(sK1)),
% 43.69/5.99    inference(cnf_transformation,[],[f79])).
% 43.69/5.99  
% 43.69/5.99  fof(f29,axiom,(
% 43.69/5.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f56,plain,(
% 43.69/5.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 43.69/5.99    inference(ennf_transformation,[],[f29])).
% 43.69/5.99  
% 43.69/5.99  fof(f57,plain,(
% 43.69/5.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 43.69/5.99    inference(flattening,[],[f56])).
% 43.69/5.99  
% 43.69/5.99  fof(f117,plain,(
% 43.69/5.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f57])).
% 43.69/5.99  
% 43.69/5.99  fof(f18,axiom,(
% 43.69/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f44,plain,(
% 43.69/5.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.69/5.99    inference(ennf_transformation,[],[f18])).
% 43.69/5.99  
% 43.69/5.99  fof(f105,plain,(
% 43.69/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.69/5.99    inference(cnf_transformation,[],[f44])).
% 43.69/5.99  
% 43.69/5.99  fof(f28,axiom,(
% 43.69/5.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f55,plain,(
% 43.69/5.99    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.69/5.99    inference(ennf_transformation,[],[f28])).
% 43.69/5.99  
% 43.69/5.99  fof(f116,plain,(
% 43.69/5.99    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.69/5.99    inference(cnf_transformation,[],[f55])).
% 43.69/5.99  
% 43.69/5.99  fof(f22,axiom,(
% 43.69/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f48,plain,(
% 43.69/5.99    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.69/5.99    inference(ennf_transformation,[],[f22])).
% 43.69/5.99  
% 43.69/5.99  fof(f109,plain,(
% 43.69/5.99    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.69/5.99    inference(cnf_transformation,[],[f48])).
% 43.69/5.99  
% 43.69/5.99  fof(f23,axiom,(
% 43.69/5.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 43.69/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/5.99  
% 43.69/5.99  fof(f110,plain,(
% 43.69/5.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 43.69/5.99    inference(cnf_transformation,[],[f23])).
% 43.69/5.99  
% 43.69/5.99  fof(f20,axiom,(
% 43.69/5.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 43.69/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/6.00  
% 43.69/6.00  fof(f45,plain,(
% 43.69/6.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 43.69/6.00    inference(ennf_transformation,[],[f20])).
% 43.69/6.00  
% 43.69/6.00  fof(f46,plain,(
% 43.69/6.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.69/6.00    inference(flattening,[],[f45])).
% 43.69/6.00  
% 43.69/6.00  fof(f107,plain,(
% 43.69/6.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.69/6.00    inference(cnf_transformation,[],[f46])).
% 43.69/6.00  
% 43.69/6.00  fof(f1,axiom,(
% 43.69/6.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 43.69/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/6.00  
% 43.69/6.00  fof(f80,plain,(
% 43.69/6.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 43.69/6.00    inference(cnf_transformation,[],[f1])).
% 43.69/6.00  
% 43.69/6.00  fof(f4,axiom,(
% 43.69/6.00    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2))),
% 43.69/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/6.00  
% 43.69/6.00  fof(f36,plain,(
% 43.69/6.00    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2) | ~r1_tarski(X2,X1))),
% 43.69/6.00    inference(ennf_transformation,[],[f4])).
% 43.69/6.00  
% 43.69/6.00  fof(f87,plain,(
% 43.69/6.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2) | ~r1_tarski(X2,X1)) )),
% 43.69/6.00    inference(cnf_transformation,[],[f36])).
% 43.69/6.00  
% 43.69/6.00  fof(f129,plain,(
% 43.69/6.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,X2) | ~r1_tarski(X2,X1)) )),
% 43.69/6.00    inference(definition_unfolding,[],[f87,f92])).
% 43.69/6.00  
% 43.69/6.00  fof(f32,axiom,(
% 43.69/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 43.69/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.69/6.00  
% 43.69/6.00  fof(f61,plain,(
% 43.69/6.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.69/6.00    inference(ennf_transformation,[],[f32])).
% 43.69/6.00  
% 43.69/6.00  fof(f62,plain,(
% 43.69/6.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.69/6.00    inference(flattening,[],[f61])).
% 43.69/6.00  
% 43.69/6.00  fof(f120,plain,(
% 43.69/6.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.69/6.00    inference(cnf_transformation,[],[f62])).
% 43.69/6.00  
% 43.69/6.00  fof(f127,plain,(
% 43.69/6.00    r2_hidden(sK2,sK4) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 43.69/6.00    inference(cnf_transformation,[],[f79])).
% 43.69/6.00  
% 43.69/6.00  fof(f126,plain,(
% 43.69/6.00    r1_tarski(sK4,sK3) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 43.69/6.00    inference(cnf_transformation,[],[f79])).
% 43.69/6.00  
% 43.69/6.00  cnf(c_19,plain,
% 43.69/6.00      ( r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
% 43.69/6.00      inference(cnf_transformation,[],[f100]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1720,plain,
% 43.69/6.00      ( r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_18,plain,
% 43.69/6.00      ( r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 43.69/6.00      inference(cnf_transformation,[],[f99]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1721,plain,
% 43.69/6.00      ( r1_xboole_0(k1_tarski(X0),X1) = iProver_top
% 43.69/6.00      | r2_hidden(X0,X1) = iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_6,plain,
% 43.69/6.00      ( r1_tarski(X0,X0) ),
% 43.69/6.00      inference(cnf_transformation,[],[f133]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1727,plain,
% 43.69/6.00      ( r1_tarski(X0,X0) = iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_13,plain,
% 43.69/6.00      ( ~ r1_xboole_0(X0,X1)
% 43.69/6.00      | ~ r1_tarski(X2,X0)
% 43.69/6.00      | ~ r1_tarski(X2,X1)
% 43.69/6.00      | k1_xboole_0 = X2 ),
% 43.69/6.00      inference(cnf_transformation,[],[f94]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1724,plain,
% 43.69/6.00      ( k1_xboole_0 = X0
% 43.69/6.00      | r1_xboole_0(X1,X2) != iProver_top
% 43.69/6.00      | r1_tarski(X0,X1) != iProver_top
% 43.69/6.00      | r1_tarski(X0,X2) != iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_7342,plain,
% 43.69/6.00      ( k1_xboole_0 = X0
% 43.69/6.00      | r1_xboole_0(X1,X0) != iProver_top
% 43.69/6.00      | r1_tarski(X0,X1) != iProver_top ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_1727,c_1724]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_52499,plain,
% 43.69/6.00      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_1727,c_7342]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_83766,plain,
% 43.69/6.00      ( k1_tarski(X0) = k1_xboole_0
% 43.69/6.00      | r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_1721,c_52499]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_17,plain,
% 43.69/6.00      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
% 43.69/6.00      inference(cnf_transformation,[],[f134]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_9,plain,
% 43.69/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 43.69/6.00      inference(cnf_transformation,[],[f131]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_11,plain,
% 43.69/6.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.69/6.00      inference(cnf_transformation,[],[f91]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1733,plain,
% 43.69/6.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 43.69/6.00      inference(light_normalisation,[status(thm)],[c_9,c_11]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1734,plain,
% 43.69/6.00      ( k1_tarski(X0) != k1_xboole_0 ),
% 43.69/6.00      inference(demodulation,[status(thm)],[c_17,c_1733]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_103369,plain,
% 43.69/6.00      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 43.69/6.00      inference(global_propositional_subsumption,
% 43.69/6.00                [status(thm)],
% 43.69/6.00                [c_83766,c_1734]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_3,plain,
% 43.69/6.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 43.69/6.00      inference(cnf_transformation,[],[f81]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1729,plain,
% 43.69/6.00      ( r2_hidden(X0,X1) != iProver_top
% 43.69/6.00      | r2_hidden(X0,X2) = iProver_top
% 43.69/6.00      | r1_tarski(X1,X2) != iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_103375,plain,
% 43.69/6.00      ( r2_hidden(X0,X1) = iProver_top
% 43.69/6.00      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_103369,c_1729]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_172837,plain,
% 43.69/6.00      ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_1720,c_103375]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_22,plain,
% 43.69/6.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 43.69/6.00      inference(cnf_transformation,[],[f102]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1717,plain,
% 43.69/6.00      ( m1_subset_1(X0,X1) = iProver_top
% 43.69/6.00      | r2_hidden(X0,X1) != iProver_top
% 43.69/6.00      | v1_xboole_0(X1) = iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_175184,plain,
% 43.69/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 43.69/6.00      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_172837,c_1717]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_25,plain,
% 43.69/6.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 43.69/6.00      inference(cnf_transformation,[],[f106]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_100,plain,
% 43.69/6.00      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_175192,plain,
% 43.69/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 43.69/6.00      inference(global_propositional_subsumption,
% 43.69/6.00                [status(thm)],
% 43.69/6.00                [c_175184,c_100]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_27,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.69/6.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 43.69/6.00      inference(cnf_transformation,[],[f108]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1712,plain,
% 43.69/6.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 43.69/6.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_175202,plain,
% 43.69/6.00      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_175192,c_1712]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_34,plain,
% 43.69/6.00      ( ~ v3_pre_topc(X0,X1)
% 43.69/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | ~ l1_pre_topc(X1)
% 43.69/6.00      | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ),
% 43.69/6.00      inference(cnf_transformation,[],[f114]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_46,negated_conjecture,
% 43.69/6.00      ( l1_pre_topc(sK1) ),
% 43.69/6.00      inference(cnf_transformation,[],[f122]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_663,plain,
% 43.69/6.00      ( ~ v3_pre_topc(X0,X1)
% 43.69/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)
% 43.69/6.00      | sK1 != X1 ),
% 43.69/6.00      inference(resolution_lifted,[status(thm)],[c_34,c_46]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_664,plain,
% 43.69/6.00      ( ~ v3_pre_topc(X0,sK1)
% 43.69/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0) ),
% 43.69/6.00      inference(unflattening,[status(thm)],[c_663]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_43,negated_conjecture,
% 43.69/6.00      ( v3_pre_topc(sK4,sK1) | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 43.69/6.00      inference(cnf_transformation,[],[f125]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_718,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)
% 43.69/6.00      | sK4 != X0
% 43.69/6.00      | sK1 != sK1 ),
% 43.69/6.00      inference(resolution_lifted,[status(thm)],[c_664,c_43]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_719,plain,
% 43.69/6.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 43.69/6.00      inference(unflattening,[status(thm)],[c_718]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_44,negated_conjecture,
% 43.69/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 43.69/6.00      inference(cnf_transformation,[],[f124]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_721,plain,
% 43.69/6.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 43.69/6.00      inference(global_propositional_subsumption,
% 43.69/6.00                [status(thm)],
% 43.69/6.00                [c_719,c_44]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1699,plain,
% 43.69/6.00      ( k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_32,plain,
% 43.69/6.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 43.69/6.00      inference(cnf_transformation,[],[f113]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_31,plain,
% 43.69/6.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 43.69/6.00      inference(cnf_transformation,[],[f112]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_472,plain,
% 43.69/6.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 43.69/6.00      inference(resolution,[status(thm)],[c_32,c_31]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_604,plain,
% 43.69/6.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 43.69/6.00      inference(resolution_lifted,[status(thm)],[c_472,c_46]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_605,plain,
% 43.69/6.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 43.69/6.00      inference(unflattening,[status(thm)],[c_604]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1739,plain,
% 43.69/6.00      ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 43.69/6.00      inference(light_normalisation,[status(thm)],[c_1699,c_605]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_45,negated_conjecture,
% 43.69/6.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 43.69/6.00      inference(cnf_transformation,[],[f123]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1787,plain,
% 43.69/6.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 43.69/6.00      inference(predicate_to_equality_rev,[status(thm)],[c_1739]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_38,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 43.69/6.00      | ~ l1_pre_topc(X1) ),
% 43.69/6.00      inference(cnf_transformation,[],[f119]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_627,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 43.69/6.00      | sK1 != X1 ),
% 43.69/6.00      inference(resolution_lifted,[status(thm)],[c_38,c_46]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_628,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 43.69/6.00      inference(unflattening,[status(thm)],[c_627]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1833,plain,
% 43.69/6.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_628]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_40,negated_conjecture,
% 43.69/6.00      ( ~ v3_pre_topc(X0,sK1)
% 43.69/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ r2_hidden(sK2,X0)
% 43.69/6.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | ~ r1_tarski(X0,sK3) ),
% 43.69/6.00      inference(cnf_transformation,[],[f128]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_37,plain,
% 43.69/6.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 43.69/6.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 43.69/6.00      | ~ v2_pre_topc(X0)
% 43.69/6.00      | ~ l1_pre_topc(X0) ),
% 43.69/6.00      inference(cnf_transformation,[],[f118]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_47,negated_conjecture,
% 43.69/6.00      ( v2_pre_topc(sK1) ),
% 43.69/6.00      inference(cnf_transformation,[],[f121]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_486,plain,
% 43.69/6.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 43.69/6.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 43.69/6.00      | ~ l1_pre_topc(X0)
% 43.69/6.00      | sK1 != X0 ),
% 43.69/6.00      inference(resolution_lifted,[status(thm)],[c_37,c_47]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_487,plain,
% 43.69/6.00      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 43.69/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ l1_pre_topc(sK1) ),
% 43.69/6.00      inference(unflattening,[status(thm)],[c_486]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_491,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
% 43.69/6.00      inference(global_propositional_subsumption,
% 43.69/6.00                [status(thm)],
% 43.69/6.00                [c_487,c_46]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_492,plain,
% 43.69/6.00      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 43.69/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 43.69/6.00      inference(renaming,[status(thm)],[c_491]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_752,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ r2_hidden(sK2,X0)
% 43.69/6.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | ~ r1_tarski(X0,sK3)
% 43.69/6.00      | k1_tops_1(sK1,X1) != X0
% 43.69/6.00      | sK1 != sK1 ),
% 43.69/6.00      inference(resolution_lifted,[status(thm)],[c_40,c_492]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_753,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 43.69/6.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
% 43.69/6.00      inference(unflattening,[status(thm)],[c_752]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_36,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | ~ l1_pre_topc(X1) ),
% 43.69/6.00      inference(cnf_transformation,[],[f117]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_639,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | sK1 != X1 ),
% 43.69/6.00      inference(resolution_lifted,[status(thm)],[c_36,c_46]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_640,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 43.69/6.00      inference(unflattening,[status(thm)],[c_639]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_757,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 43.69/6.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
% 43.69/6.00      inference(global_propositional_subsumption,
% 43.69/6.00                [status(thm)],
% 43.69/6.00                [c_753,c_640]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1853,plain,
% 43.69/6.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_757]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_2562,plain,
% 43.69/6.00      ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 43.69/6.00      inference(global_propositional_subsumption,
% 43.69/6.00                [status(thm)],
% 43.69/6.00                [c_1739,c_45,c_1787,c_1833,c_1853]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_177700,plain,
% 43.69/6.00      ( k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4)) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
% 43.69/6.00      inference(demodulation,[status(thm)],[c_175202,c_2562]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1706,plain,
% 43.69/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1735,plain,
% 43.69/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 43.69/6.00      inference(light_normalisation,[status(thm)],[c_1706,c_605]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_50,plain,
% 43.69/6.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1834,plain,
% 43.69/6.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 43.69/6.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_1833]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1854,plain,
% 43.69/6.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
% 43.69/6.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_1853]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_2541,plain,
% 43.69/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 43.69/6.00      inference(global_propositional_subsumption,
% 43.69/6.00                [status(thm)],
% 43.69/6.00                [c_1735,c_50,c_1834,c_1854]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_24,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.69/6.00      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 43.69/6.00      inference(cnf_transformation,[],[f105]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1715,plain,
% 43.69/6.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 43.69/6.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_5716,plain,
% 43.69/6.00      ( k3_subset_1(k2_struct_0(sK1),sK4) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_2541,c_1715]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_35,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | ~ l1_pre_topc(X1)
% 43.69/6.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 43.69/6.00      inference(cnf_transformation,[],[f116]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_651,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 43.69/6.00      | sK1 != X1 ),
% 43.69/6.00      inference(resolution_lifted,[status(thm)],[c_35,c_46]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_652,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
% 43.69/6.00      inference(unflattening,[status(thm)],[c_651]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1701,plain,
% 43.69/6.00      ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
% 43.69/6.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1738,plain,
% 43.69/6.00      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
% 43.69/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 43.69/6.00      inference(light_normalisation,[status(thm)],[c_1701,c_605]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_2547,plain,
% 43.69/6.00      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_2541,c_1738]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_6254,plain,
% 43.69/6.00      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
% 43.69/6.00      inference(demodulation,[status(thm)],[c_5716,c_2547]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_177775,plain,
% 43.69/6.00      ( k3_subset_1(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK4)) = k1_tops_1(sK1,sK4) ),
% 43.69/6.00      inference(demodulation,[status(thm)],[c_177700,c_6254]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_175203,plain,
% 43.69/6.00      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_175192,c_1715]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_175646,plain,
% 43.69/6.00      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 43.69/6.00      inference(light_normalisation,[status(thm)],[c_175203,c_1733]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_28,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.69/6.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 43.69/6.00      | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
% 43.69/6.00      inference(cnf_transformation,[],[f109]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1711,plain,
% 43.69/6.00      ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
% 43.69/6.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 43.69/6.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_2878,plain,
% 43.69/6.00      ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),X0),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),X0,sK4))
% 43.69/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_2541,c_1711]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_175565,plain,
% 43.69/6.00      ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_struct_0(sK1)),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_175192,c_2878]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_175648,plain,
% 43.69/6.00      ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) ),
% 43.69/6.00      inference(demodulation,[status(thm)],[c_175646,c_175565]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_29,plain,
% 43.69/6.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 43.69/6.00      inference(cnf_transformation,[],[f110]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1710,plain,
% 43.69/6.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_26,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.69/6.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 43.69/6.00      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 43.69/6.00      inference(cnf_transformation,[],[f107]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1713,plain,
% 43.69/6.00      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 43.69/6.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 43.69/6.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_3731,plain,
% 43.69/6.00      ( k4_subset_1(k2_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
% 43.69/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_2541,c_1713]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_4338,plain,
% 43.69/6.00      ( k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) = k2_xboole_0(k1_xboole_0,sK4) ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_1710,c_3731]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_0,plain,
% 43.69/6.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 43.69/6.00      inference(cnf_transformation,[],[f80]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_7,plain,
% 43.69/6.00      ( ~ r1_tarski(X0,X1)
% 43.69/6.00      | k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X0)))) = k4_xboole_0(X2,X0) ),
% 43.69/6.00      inference(cnf_transformation,[],[f129]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1726,plain,
% 43.69/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,X2)
% 43.69/6.00      | r1_tarski(X2,X1) != iProver_top ),
% 43.69/6.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_7369,plain,
% 43.69/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1)))) = k4_xboole_0(X0,X1) ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_1727,c_1726]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_7376,plain,
% 43.69/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
% 43.69/6.00      inference(demodulation,[status(thm)],[c_7369,c_11,c_1733]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_7473,plain,
% 43.69/6.00      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_11,c_7376]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_7483,plain,
% 43.69/6.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.69/6.00      inference(light_normalisation,[status(thm)],[c_7473,c_11]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_7494,plain,
% 43.69/6.00      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 43.69/6.00      inference(superposition,[status(thm)],[c_0,c_7483]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_9517,plain,
% 43.69/6.00      ( k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) = sK4 ),
% 43.69/6.00      inference(demodulation,[status(thm)],[c_4338,c_7494]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_175652,plain,
% 43.69/6.00      ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = sK4 ),
% 43.69/6.00      inference(light_normalisation,[status(thm)],[c_175648,c_9517]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_175653,plain,
% 43.69/6.00      ( k3_subset_1(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK4)) = sK4 ),
% 43.69/6.00      inference(demodulation,[status(thm)],[c_175202,c_175652]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_177776,plain,
% 43.69/6.00      ( k1_tops_1(sK1,sK4) = sK4 ),
% 43.69/6.00      inference(light_normalisation,[status(thm)],[c_177775,c_175653]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1107,plain,
% 43.69/6.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.69/6.00      theory(equality) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1884,plain,
% 43.69/6.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK2,X2) | X2 != X1 | sK2 != X0 ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_1107]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_3134,plain,
% 43.69/6.00      ( r2_hidden(sK2,X0)
% 43.69/6.00      | ~ r2_hidden(sK2,sK4)
% 43.69/6.00      | X0 != sK4
% 43.69/6.00      | sK2 != sK2 ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_1884]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_7562,plain,
% 43.69/6.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 43.69/6.00      | ~ r2_hidden(sK2,sK4)
% 43.69/6.00      | k1_tops_1(sK1,sK4) != sK4
% 43.69/6.00      | sK2 != sK2 ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_3134]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1881,plain,
% 43.69/6.00      ( ~ r2_hidden(sK2,X0) | r2_hidden(sK2,X1) | ~ r1_tarski(X0,X1) ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_3]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_2288,plain,
% 43.69/6.00      ( ~ r2_hidden(sK2,X0)
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | ~ r1_tarski(X0,k1_tops_1(sK1,sK3)) ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_1881]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_2621,plain,
% 43.69/6.00      ( ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | ~ r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_2288]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_2909,plain,
% 43.69/6.00      ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 43.69/6.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 43.69/6.00      | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_2621]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1103,plain,( X0 = X0 ),theory(equality) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_2859,plain,
% 43.69/6.00      ( sK2 = sK2 ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_1103]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_39,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | ~ r1_tarski(X0,X2)
% 43.69/6.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 43.69/6.00      | ~ l1_pre_topc(X1) ),
% 43.69/6.00      inference(cnf_transformation,[],[f120]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_609,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 43.69/6.00      | ~ r1_tarski(X0,X2)
% 43.69/6.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 43.69/6.00      | sK1 != X1 ),
% 43.69/6.00      inference(resolution_lifted,[status(thm)],[c_39,c_46]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_610,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ r1_tarski(X1,X0)
% 43.69/6.00      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 43.69/6.00      inference(unflattening,[status(thm)],[c_609]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_1953,plain,
% 43.69/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ r1_tarski(X0,sK3)
% 43.69/6.00      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_610]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_2170,plain,
% 43.69/6.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 43.69/6.00      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3))
% 43.69/6.00      | ~ r1_tarski(sK4,sK3) ),
% 43.69/6.00      inference(instantiation,[status(thm)],[c_1953]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_41,negated_conjecture,
% 43.69/6.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r2_hidden(sK2,sK4) ),
% 43.69/6.00      inference(cnf_transformation,[],[f127]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(c_42,negated_conjecture,
% 43.69/6.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r1_tarski(sK4,sK3) ),
% 43.69/6.00      inference(cnf_transformation,[],[f126]) ).
% 43.69/6.00  
% 43.69/6.00  cnf(contradiction,plain,
% 43.69/6.00      ( $false ),
% 43.69/6.00      inference(minisat,
% 43.69/6.00                [status(thm)],
% 43.69/6.00                [c_177776,c_7562,c_2909,c_2859,c_2170,c_1853,c_1833,c_41,
% 43.69/6.00                 c_42,c_44,c_45]) ).
% 43.69/6.00  
% 43.69/6.00  
% 43.69/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 43.69/6.00  
% 43.69/6.00  ------                               Statistics
% 43.69/6.00  
% 43.69/6.00  ------ General
% 43.69/6.00  
% 43.69/6.00  abstr_ref_over_cycles:                  0
% 43.69/6.00  abstr_ref_under_cycles:                 0
% 43.69/6.00  gc_basic_clause_elim:                   0
% 43.69/6.00  forced_gc_time:                         0
% 43.69/6.00  parsing_time:                           0.012
% 43.69/6.00  unif_index_cands_time:                  0.
% 43.69/6.00  unif_index_add_time:                    0.
% 43.69/6.00  orderings_time:                         0.
% 43.69/6.00  out_proof_time:                         0.026
% 43.69/6.00  total_time:                             5.129
% 43.69/6.00  num_of_symbols:                         57
% 43.69/6.00  num_of_terms:                           112338
% 43.69/6.00  
% 43.69/6.00  ------ Preprocessing
% 43.69/6.00  
% 43.69/6.00  num_of_splits:                          0
% 43.69/6.00  num_of_split_atoms:                     0
% 43.69/6.00  num_of_reused_defs:                     0
% 43.69/6.00  num_eq_ax_congr_red:                    19
% 43.69/6.00  num_of_sem_filtered_clauses:            1
% 43.69/6.00  num_of_subtypes:                        0
% 43.69/6.00  monotx_restored_types:                  0
% 43.69/6.00  sat_num_of_epr_types:                   0
% 43.69/6.00  sat_num_of_non_cyclic_types:            0
% 43.69/6.00  sat_guarded_non_collapsed_types:        0
% 43.69/6.00  num_pure_diseq_elim:                    0
% 43.69/6.00  simp_replaced_by:                       0
% 43.69/6.00  res_preprocessed:                       211
% 43.69/6.00  prep_upred:                             0
% 43.69/6.00  prep_unflattend:                        28
% 43.69/6.00  smt_new_axioms:                         0
% 43.69/6.00  pred_elim_cands:                        5
% 43.69/6.00  pred_elim:                              4
% 43.69/6.00  pred_elim_cl:                           4
% 43.69/6.00  pred_elim_cycles:                       7
% 43.69/6.00  merged_defs:                            0
% 43.69/6.00  merged_defs_ncl:                        0
% 43.69/6.00  bin_hyper_res:                          0
% 43.69/6.00  prep_cycles:                            4
% 43.69/6.00  pred_elim_time:                         0.008
% 43.69/6.00  splitting_time:                         0.
% 43.69/6.00  sem_filter_time:                        0.
% 43.69/6.00  monotx_time:                            0.001
% 43.69/6.00  subtype_inf_time:                       0.
% 43.69/6.00  
% 43.69/6.00  ------ Problem properties
% 43.69/6.00  
% 43.69/6.00  clauses:                                43
% 43.69/6.00  conjectures:                            4
% 43.69/6.00  epr:                                    8
% 43.69/6.00  horn:                                   34
% 43.69/6.00  ground:                                 6
% 43.69/6.00  unary:                                  12
% 43.69/6.00  binary:                                 18
% 43.69/6.00  lits:                                   92
% 43.69/6.00  lits_eq:                                22
% 43.69/6.00  fd_pure:                                0
% 43.69/6.00  fd_pseudo:                              0
% 43.69/6.00  fd_cond:                                1
% 43.69/6.00  fd_pseudo_cond:                         2
% 43.69/6.00  ac_symbols:                             0
% 43.69/6.00  
% 43.69/6.00  ------ Propositional Solver
% 43.69/6.00  
% 43.69/6.00  prop_solver_calls:                      56
% 43.69/6.00  prop_fast_solver_calls:                 4011
% 43.69/6.00  smt_solver_calls:                       0
% 43.69/6.00  smt_fast_solver_calls:                  0
% 43.69/6.00  prop_num_of_clauses:                    55583
% 43.69/6.00  prop_preprocess_simplified:             86585
% 43.69/6.00  prop_fo_subsumed:                       68
% 43.69/6.00  prop_solver_time:                       0.
% 43.69/6.00  smt_solver_time:                        0.
% 43.69/6.00  smt_fast_solver_time:                   0.
% 43.69/6.00  prop_fast_solver_time:                  0.
% 43.69/6.00  prop_unsat_core_time:                   0.005
% 43.69/6.00  
% 43.69/6.00  ------ QBF
% 43.69/6.00  
% 43.69/6.00  qbf_q_res:                              0
% 43.69/6.00  qbf_num_tautologies:                    0
% 43.69/6.00  qbf_prep_cycles:                        0
% 43.69/6.00  
% 43.69/6.00  ------ BMC1
% 43.69/6.00  
% 43.69/6.00  bmc1_current_bound:                     -1
% 43.69/6.00  bmc1_last_solved_bound:                 -1
% 43.69/6.00  bmc1_unsat_core_size:                   -1
% 43.69/6.00  bmc1_unsat_core_parents_size:           -1
% 43.69/6.00  bmc1_merge_next_fun:                    0
% 43.69/6.00  bmc1_unsat_core_clauses_time:           0.
% 43.69/6.00  
% 43.69/6.00  ------ Instantiation
% 43.69/6.00  
% 43.69/6.00  inst_num_of_clauses:                    8937
% 43.69/6.00  inst_num_in_passive:                    2975
% 43.69/6.00  inst_num_in_active:                     5799
% 43.69/6.00  inst_num_in_unprocessed:                2230
% 43.69/6.00  inst_num_of_loops:                      7739
% 43.69/6.00  inst_num_of_learning_restarts:          1
% 43.69/6.00  inst_num_moves_active_passive:          1934
% 43.69/6.00  inst_lit_activity:                      0
% 43.69/6.00  inst_lit_activity_moves:                0
% 43.69/6.00  inst_num_tautologies:                   0
% 43.69/6.00  inst_num_prop_implied:                  0
% 43.69/6.00  inst_num_existing_simplified:           0
% 43.69/6.00  inst_num_eq_res_simplified:             0
% 43.69/6.00  inst_num_child_elim:                    0
% 43.69/6.00  inst_num_of_dismatching_blockings:      17861
% 43.69/6.00  inst_num_of_non_proper_insts:           25568
% 43.69/6.00  inst_num_of_duplicates:                 0
% 43.69/6.00  inst_inst_num_from_inst_to_res:         0
% 43.69/6.00  inst_dismatching_checking_time:         0.
% 43.69/6.00  
% 43.69/6.00  ------ Resolution
% 43.69/6.00  
% 43.69/6.00  res_num_of_clauses:                     60
% 43.69/6.00  res_num_in_passive:                     60
% 43.69/6.00  res_num_in_active:                      0
% 43.69/6.00  res_num_of_loops:                       215
% 43.69/6.00  res_forward_subset_subsumed:            628
% 43.69/6.00  res_backward_subset_subsumed:           12
% 43.69/6.00  res_forward_subsumed:                   0
% 43.69/6.00  res_backward_subsumed:                  0
% 43.69/6.00  res_forward_subsumption_resolution:     0
% 43.69/6.00  res_backward_subsumption_resolution:    0
% 43.69/6.00  res_clause_to_clause_subsumption:       65781
% 43.69/6.00  res_orphan_elimination:                 0
% 43.69/6.00  res_tautology_del:                      1836
% 43.69/6.00  res_num_eq_res_simplified:              0
% 43.69/6.00  res_num_sel_changes:                    0
% 43.69/6.00  res_moves_from_active_to_pass:          0
% 43.69/6.00  
% 43.69/6.00  ------ Superposition
% 43.69/6.00  
% 43.69/6.00  sup_time_total:                         0.
% 43.69/6.00  sup_time_generating:                    0.
% 43.69/6.00  sup_time_sim_full:                      0.
% 43.69/6.00  sup_time_sim_immed:                     0.
% 43.69/6.00  
% 43.69/6.00  sup_num_of_clauses:                     6687
% 43.69/6.00  sup_num_in_active:                      1358
% 43.69/6.00  sup_num_in_passive:                     5329
% 43.69/6.00  sup_num_of_loops:                       1547
% 43.69/6.00  sup_fw_superposition:                   11825
% 43.69/6.00  sup_bw_superposition:                   9604
% 43.69/6.00  sup_immediate_simplified:               13406
% 43.69/6.00  sup_given_eliminated:                   26
% 43.69/6.00  comparisons_done:                       0
% 43.69/6.00  comparisons_avoided:                    207
% 43.69/6.00  
% 43.69/6.00  ------ Simplifications
% 43.69/6.00  
% 43.69/6.00  
% 43.69/6.00  sim_fw_subset_subsumed:                 994
% 43.69/6.00  sim_bw_subset_subsumed:                 10
% 43.69/6.00  sim_fw_subsumed:                        2246
% 43.69/6.00  sim_bw_subsumed:                        43
% 43.69/6.00  sim_fw_subsumption_res:                 0
% 43.69/6.00  sim_bw_subsumption_res:                 0
% 43.69/6.00  sim_tautology_del:                      13
% 43.69/6.00  sim_eq_tautology_del:                   4866
% 43.69/6.00  sim_eq_res_simp:                        0
% 43.69/6.00  sim_fw_demodulated:                     8627
% 43.69/6.00  sim_bw_demodulated:                     332
% 43.69/6.00  sim_light_normalised:                   5468
% 43.69/6.00  sim_joinable_taut:                      0
% 43.69/6.00  sim_joinable_simp:                      0
% 43.69/6.00  sim_ac_normalised:                      0
% 43.69/6.00  sim_smt_subsumption:                    0
% 43.69/6.00  
%------------------------------------------------------------------------------
