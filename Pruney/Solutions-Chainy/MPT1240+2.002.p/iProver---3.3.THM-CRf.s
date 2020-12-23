%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:57 EST 2020

% Result     : Theorem 11.86s
% Output     : CNFRefutation 11.86s
% Verified   : 
% Statistics : Number of formulae       :  241 (2315 expanded)
%              Number of clauses        :  136 ( 740 expanded)
%              Number of leaves         :   33 ( 526 expanded)
%              Depth                    :   27
%              Number of atoms          :  717 (14122 expanded)
%              Number of equality atoms :  209 (1221 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f38])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

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
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f130,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f132,plain,(
    ! [X1] : k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1) ),
    inference(equality_resolution,[],[f97])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f129,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f88,f90])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f34])).

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

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

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

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f18,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f22,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f32,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,negated_conjecture,(
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
    inference(negated_conjecture,[],[f32])).

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
    inference(ennf_transformation,[],[f33])).

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

fof(f123,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f79])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f112,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f111,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f121,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f122,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f79])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f127,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r1_tarski(X3,sK3)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f120,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f26])).

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

fof(f113,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f124,plain,
    ( v3_pre_topc(sK4,sK1)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f79])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

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

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f126,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f79])).

fof(f125,plain,
    ( r1_tarski(sK4,sK3)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_18,plain,
    ( r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1607,plain,
    ( r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1608,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,X3)
    | X2 = X1
    | k2_xboole_0(X2,X0) != k2_xboole_0(X3,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1611,plain,
    ( X0 = X1
    | k2_xboole_0(X0,X2) != k2_xboole_0(X3,X1)
    | r1_xboole_0(X2,X1) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6251,plain,
    ( X0 = X1
    | k2_xboole_0(X2,X0) != X1
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1611])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1615,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1610,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3669,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1610])).

cnf(c_3829,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1615,c_3669])).

cnf(c_6756,plain,
    ( r1_xboole_0(X1,X2) != iProver_top
    | k2_xboole_0(X2,X0) != X1
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6251,c_3829])).

cnf(c_6757,plain,
    ( X0 = X1
    | k2_xboole_0(X2,X0) != X1
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6756])).

cnf(c_6760,plain,
    ( X0 != X1
    | k1_xboole_0 = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_6757])).

cnf(c_6769,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_6760])).

cnf(c_9065,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1608,c_6769])).

cnf(c_17,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1621,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8,c_9])).

cnf(c_1622,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17,c_1621])).

cnf(c_11095,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9065,c_1622])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1617,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11101,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11095,c_1617])).

cnf(c_11940,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_11101])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1604,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11946,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11940,c_1604])).

cnf(c_24,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_99,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_12040,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11946,c_99])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1598,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12053,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X1),X0) = k3_subset_1(X0,k7_subset_1(X0,X1,X0))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12040,c_1598])).

cnf(c_46535,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X0),X0) = k3_subset_1(X0,k7_subset_1(X0,X0,X0)) ),
    inference(superposition,[status(thm)],[c_12040,c_12053])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1602,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12049,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_12040,c_1602])).

cnf(c_12092,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12049,c_1621])).

cnf(c_28,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1597,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1600,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12052,plain,
    ( k4_subset_1(X0,X1,X0) = k2_xboole_0(X1,X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12040,c_1600])).

cnf(c_23355,plain,
    ( k4_subset_1(X0,k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1597,c_12052])).

cnf(c_46539,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,X0,X0)) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_46535,c_12092,c_23355])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1599,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12048,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_12040,c_1599])).

cnf(c_46540,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_46539,c_12048])).

cnf(c_4818,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1597,c_1602])).

cnf(c_4822,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4818,c_9])).

cnf(c_46541,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_46540,c_1621,c_4822])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1593,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_31,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_30,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_478,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_31,c_30])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_538,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_478,c_45])).

cnf(c_539,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_1623,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1593,c_539])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_45])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_1722,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_1723,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1722])).

cnf(c_39,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_36,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_492,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_46])).

cnf(c_493,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_45])).

cnf(c_498,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_497])).

cnf(c_686,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X0,sK3)
    | k1_tops_1(sK1,X1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_498])).

cnf(c_687,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_45])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_691,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_687,c_574])).

cnf(c_1742,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_1743,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1742])).

cnf(c_2437,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1623,c_49,c_1723,c_1743])).

cnf(c_4820,plain,
    ( k3_subset_1(k2_struct_0(sK1),sK4) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
    inference(superposition,[status(thm)],[c_2437,c_1602])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_585,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_45])).

cnf(c_586,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_1588,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_1626,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1588,c_539])).

cnf(c_2443,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
    inference(superposition,[status(thm)],[c_2437,c_1626])).

cnf(c_5222,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
    inference(demodulation,[status(thm)],[c_4820,c_2443])).

cnf(c_2781,plain,
    ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),X0),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_1598])).

cnf(c_12072,plain,
    ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_struct_0(sK1)),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) ),
    inference(superposition,[status(thm)],[c_12040,c_2781])).

cnf(c_12094,plain,
    ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) ),
    inference(demodulation,[status(thm)],[c_12092,c_12072])).

cnf(c_3479,plain,
    ( k4_subset_1(k2_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_1600])).

cnf(c_4284,plain,
    ( k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) = k2_xboole_0(k1_xboole_0,sK4) ),
    inference(superposition,[status(thm)],[c_1597,c_3479])).

cnf(c_12098,plain,
    ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k2_xboole_0(k1_xboole_0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_12094,c_4284])).

cnf(c_12099,plain,
    ( k3_subset_1(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK4)) = k2_xboole_0(k1_xboole_0,sK4) ),
    inference(demodulation,[status(thm)],[c_12048,c_12098])).

cnf(c_33,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_597,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_45])).

cnf(c_598,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_42,negated_conjecture,
    ( v3_pre_topc(sK4,sK1)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)
    | sK4 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_598,c_42])).

cnf(c_653,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_655,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_43])).

cnf(c_1586,plain,
    ( k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_1627,plain,
    ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1586,c_539])).

cnf(c_1663,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1627])).

cnf(c_2458,plain,
    ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1627,c_44,c_1663,c_1722,c_1742])).

cnf(c_13083,plain,
    ( k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4)) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
    inference(demodulation,[status(thm)],[c_12048,c_2458])).

cnf(c_24496,plain,
    ( k1_tops_1(sK1,sK4) = k2_xboole_0(k1_xboole_0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_5222,c_5222,c_12099,c_13083])).

cnf(c_46582,plain,
    ( k1_tops_1(sK1,sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_46541,c_24496])).

cnf(c_981,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1773,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_3037,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,sK4)
    | X0 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_7071,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | ~ r2_hidden(sK2,sK4)
    | k1_tops_1(sK1,sK4) != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3037])).

cnf(c_1770,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2177,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X0,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1770])).

cnf(c_2517,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2177])).

cnf(c_2812,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_978,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2762,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_45])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_1842,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK3)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_2059,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3))
    | ~ r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1842])).

cnf(c_40,negated_conjecture,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_41,negated_conjecture,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f125])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46582,c_7071,c_2812,c_2762,c_2059,c_1742,c_1722,c_40,c_41,c_43,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 15:33:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 11.86/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.86/2.00  
% 11.86/2.00  ------  iProver source info
% 11.86/2.00  
% 11.86/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.86/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.86/2.00  git: non_committed_changes: false
% 11.86/2.00  git: last_make_outside_of_git: false
% 11.86/2.00  
% 11.86/2.00  ------ 
% 11.86/2.00  
% 11.86/2.00  ------ Input Options
% 11.86/2.00  
% 11.86/2.00  --out_options                           all
% 11.86/2.00  --tptp_safe_out                         true
% 11.86/2.00  --problem_path                          ""
% 11.86/2.00  --include_path                          ""
% 11.86/2.00  --clausifier                            res/vclausify_rel
% 11.86/2.00  --clausifier_options                    ""
% 11.86/2.00  --stdin                                 false
% 11.86/2.00  --stats_out                             all
% 11.86/2.00  
% 11.86/2.00  ------ General Options
% 11.86/2.00  
% 11.86/2.00  --fof                                   false
% 11.86/2.00  --time_out_real                         305.
% 11.86/2.00  --time_out_virtual                      -1.
% 11.86/2.00  --symbol_type_check                     false
% 11.86/2.00  --clausify_out                          false
% 11.86/2.00  --sig_cnt_out                           false
% 11.86/2.00  --trig_cnt_out                          false
% 11.86/2.00  --trig_cnt_out_tolerance                1.
% 11.86/2.00  --trig_cnt_out_sk_spl                   false
% 11.86/2.00  --abstr_cl_out                          false
% 11.86/2.00  
% 11.86/2.00  ------ Global Options
% 11.86/2.00  
% 11.86/2.00  --schedule                              default
% 11.86/2.00  --add_important_lit                     false
% 11.86/2.00  --prop_solver_per_cl                    1000
% 11.86/2.00  --min_unsat_core                        false
% 11.86/2.00  --soft_assumptions                      false
% 11.86/2.00  --soft_lemma_size                       3
% 11.86/2.00  --prop_impl_unit_size                   0
% 11.86/2.00  --prop_impl_unit                        []
% 11.86/2.00  --share_sel_clauses                     true
% 11.86/2.00  --reset_solvers                         false
% 11.86/2.00  --bc_imp_inh                            [conj_cone]
% 11.86/2.00  --conj_cone_tolerance                   3.
% 11.86/2.00  --extra_neg_conj                        none
% 11.86/2.00  --large_theory_mode                     true
% 11.86/2.00  --prolific_symb_bound                   200
% 11.86/2.00  --lt_threshold                          2000
% 11.86/2.00  --clause_weak_htbl                      true
% 11.86/2.00  --gc_record_bc_elim                     false
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing Options
% 11.86/2.00  
% 11.86/2.00  --preprocessing_flag                    true
% 11.86/2.00  --time_out_prep_mult                    0.1
% 11.86/2.00  --splitting_mode                        input
% 11.86/2.00  --splitting_grd                         true
% 11.86/2.00  --splitting_cvd                         false
% 11.86/2.00  --splitting_cvd_svl                     false
% 11.86/2.00  --splitting_nvd                         32
% 11.86/2.00  --sub_typing                            true
% 11.86/2.00  --prep_gs_sim                           true
% 11.86/2.00  --prep_unflatten                        true
% 11.86/2.00  --prep_res_sim                          true
% 11.86/2.00  --prep_upred                            true
% 11.86/2.00  --prep_sem_filter                       exhaustive
% 11.86/2.00  --prep_sem_filter_out                   false
% 11.86/2.00  --pred_elim                             true
% 11.86/2.00  --res_sim_input                         true
% 11.86/2.00  --eq_ax_congr_red                       true
% 11.86/2.00  --pure_diseq_elim                       true
% 11.86/2.00  --brand_transform                       false
% 11.86/2.00  --non_eq_to_eq                          false
% 11.86/2.00  --prep_def_merge                        true
% 11.86/2.00  --prep_def_merge_prop_impl              false
% 11.86/2.00  --prep_def_merge_mbd                    true
% 11.86/2.00  --prep_def_merge_tr_red                 false
% 11.86/2.00  --prep_def_merge_tr_cl                  false
% 11.86/2.00  --smt_preprocessing                     true
% 11.86/2.00  --smt_ac_axioms                         fast
% 11.86/2.00  --preprocessed_out                      false
% 11.86/2.00  --preprocessed_stats                    false
% 11.86/2.00  
% 11.86/2.00  ------ Abstraction refinement Options
% 11.86/2.00  
% 11.86/2.00  --abstr_ref                             []
% 11.86/2.00  --abstr_ref_prep                        false
% 11.86/2.00  --abstr_ref_until_sat                   false
% 11.86/2.00  --abstr_ref_sig_restrict                funpre
% 11.86/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.86/2.00  --abstr_ref_under                       []
% 11.86/2.00  
% 11.86/2.00  ------ SAT Options
% 11.86/2.00  
% 11.86/2.00  --sat_mode                              false
% 11.86/2.00  --sat_fm_restart_options                ""
% 11.86/2.00  --sat_gr_def                            false
% 11.86/2.00  --sat_epr_types                         true
% 11.86/2.00  --sat_non_cyclic_types                  false
% 11.86/2.00  --sat_finite_models                     false
% 11.86/2.00  --sat_fm_lemmas                         false
% 11.86/2.00  --sat_fm_prep                           false
% 11.86/2.00  --sat_fm_uc_incr                        true
% 11.86/2.00  --sat_out_model                         small
% 11.86/2.00  --sat_out_clauses                       false
% 11.86/2.00  
% 11.86/2.00  ------ QBF Options
% 11.86/2.00  
% 11.86/2.00  --qbf_mode                              false
% 11.86/2.00  --qbf_elim_univ                         false
% 11.86/2.00  --qbf_dom_inst                          none
% 11.86/2.00  --qbf_dom_pre_inst                      false
% 11.86/2.00  --qbf_sk_in                             false
% 11.86/2.00  --qbf_pred_elim                         true
% 11.86/2.00  --qbf_split                             512
% 11.86/2.00  
% 11.86/2.00  ------ BMC1 Options
% 11.86/2.00  
% 11.86/2.00  --bmc1_incremental                      false
% 11.86/2.00  --bmc1_axioms                           reachable_all
% 11.86/2.00  --bmc1_min_bound                        0
% 11.86/2.00  --bmc1_max_bound                        -1
% 11.86/2.00  --bmc1_max_bound_default                -1
% 11.86/2.00  --bmc1_symbol_reachability              true
% 11.86/2.00  --bmc1_property_lemmas                  false
% 11.86/2.00  --bmc1_k_induction                      false
% 11.86/2.00  --bmc1_non_equiv_states                 false
% 11.86/2.00  --bmc1_deadlock                         false
% 11.86/2.00  --bmc1_ucm                              false
% 11.86/2.00  --bmc1_add_unsat_core                   none
% 11.86/2.00  --bmc1_unsat_core_children              false
% 11.86/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.86/2.00  --bmc1_out_stat                         full
% 11.86/2.00  --bmc1_ground_init                      false
% 11.86/2.00  --bmc1_pre_inst_next_state              false
% 11.86/2.00  --bmc1_pre_inst_state                   false
% 11.86/2.00  --bmc1_pre_inst_reach_state             false
% 11.86/2.00  --bmc1_out_unsat_core                   false
% 11.86/2.00  --bmc1_aig_witness_out                  false
% 11.86/2.00  --bmc1_verbose                          false
% 11.86/2.00  --bmc1_dump_clauses_tptp                false
% 11.86/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.86/2.00  --bmc1_dump_file                        -
% 11.86/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.86/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.86/2.00  --bmc1_ucm_extend_mode                  1
% 11.86/2.00  --bmc1_ucm_init_mode                    2
% 11.86/2.00  --bmc1_ucm_cone_mode                    none
% 11.86/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.86/2.00  --bmc1_ucm_relax_model                  4
% 11.86/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.86/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.86/2.00  --bmc1_ucm_layered_model                none
% 11.86/2.00  --bmc1_ucm_max_lemma_size               10
% 11.86/2.00  
% 11.86/2.00  ------ AIG Options
% 11.86/2.00  
% 11.86/2.00  --aig_mode                              false
% 11.86/2.00  
% 11.86/2.00  ------ Instantiation Options
% 11.86/2.00  
% 11.86/2.00  --instantiation_flag                    true
% 11.86/2.00  --inst_sos_flag                         true
% 11.86/2.00  --inst_sos_phase                        true
% 11.86/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel_side                     num_symb
% 11.86/2.00  --inst_solver_per_active                1400
% 11.86/2.00  --inst_solver_calls_frac                1.
% 11.86/2.00  --inst_passive_queue_type               priority_queues
% 11.86/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.86/2.00  --inst_passive_queues_freq              [25;2]
% 11.86/2.00  --inst_dismatching                      true
% 11.86/2.00  --inst_eager_unprocessed_to_passive     true
% 11.86/2.00  --inst_prop_sim_given                   true
% 11.86/2.00  --inst_prop_sim_new                     false
% 11.86/2.00  --inst_subs_new                         false
% 11.86/2.00  --inst_eq_res_simp                      false
% 11.86/2.00  --inst_subs_given                       false
% 11.86/2.00  --inst_orphan_elimination               true
% 11.86/2.00  --inst_learning_loop_flag               true
% 11.86/2.00  --inst_learning_start                   3000
% 11.86/2.00  --inst_learning_factor                  2
% 11.86/2.00  --inst_start_prop_sim_after_learn       3
% 11.86/2.00  --inst_sel_renew                        solver
% 11.86/2.00  --inst_lit_activity_flag                true
% 11.86/2.00  --inst_restr_to_given                   false
% 11.86/2.00  --inst_activity_threshold               500
% 11.86/2.00  --inst_out_proof                        true
% 11.86/2.00  
% 11.86/2.00  ------ Resolution Options
% 11.86/2.00  
% 11.86/2.00  --resolution_flag                       true
% 11.86/2.00  --res_lit_sel                           adaptive
% 11.86/2.00  --res_lit_sel_side                      none
% 11.86/2.00  --res_ordering                          kbo
% 11.86/2.00  --res_to_prop_solver                    active
% 11.86/2.00  --res_prop_simpl_new                    false
% 11.86/2.00  --res_prop_simpl_given                  true
% 11.86/2.00  --res_passive_queue_type                priority_queues
% 11.86/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.86/2.00  --res_passive_queues_freq               [15;5]
% 11.86/2.00  --res_forward_subs                      full
% 11.86/2.00  --res_backward_subs                     full
% 11.86/2.00  --res_forward_subs_resolution           true
% 11.86/2.00  --res_backward_subs_resolution          true
% 11.86/2.00  --res_orphan_elimination                true
% 11.86/2.00  --res_time_limit                        2.
% 11.86/2.00  --res_out_proof                         true
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Options
% 11.86/2.00  
% 11.86/2.00  --superposition_flag                    true
% 11.86/2.00  --sup_passive_queue_type                priority_queues
% 11.86/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.86/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.86/2.00  --demod_completeness_check              fast
% 11.86/2.00  --demod_use_ground                      true
% 11.86/2.00  --sup_to_prop_solver                    passive
% 11.86/2.00  --sup_prop_simpl_new                    true
% 11.86/2.00  --sup_prop_simpl_given                  true
% 11.86/2.00  --sup_fun_splitting                     true
% 11.86/2.00  --sup_smt_interval                      50000
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Simplification Setup
% 11.86/2.00  
% 11.86/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.86/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.86/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_immed_triv                        [TrivRules]
% 11.86/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_bw_main                     []
% 11.86/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.86/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_input_bw                          []
% 11.86/2.00  
% 11.86/2.00  ------ Combination Options
% 11.86/2.00  
% 11.86/2.00  --comb_res_mult                         3
% 11.86/2.00  --comb_sup_mult                         2
% 11.86/2.00  --comb_inst_mult                        10
% 11.86/2.00  
% 11.86/2.00  ------ Debug Options
% 11.86/2.00  
% 11.86/2.00  --dbg_backtrace                         false
% 11.86/2.00  --dbg_dump_prop_clauses                 false
% 11.86/2.00  --dbg_dump_prop_clauses_file            -
% 11.86/2.00  --dbg_out_stat                          false
% 11.86/2.00  ------ Parsing...
% 11.86/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  ------ Proving...
% 11.86/2.00  ------ Problem Properties 
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  clauses                                 42
% 11.86/2.00  conjectures                             4
% 11.86/2.00  EPR                                     9
% 11.86/2.00  Horn                                    33
% 11.86/2.00  unary                                   11
% 11.86/2.00  binary                                  17
% 11.86/2.00  lits                                    93
% 11.86/2.00  lits eq                                 21
% 11.86/2.00  fd_pure                                 0
% 11.86/2.00  fd_pseudo                               0
% 11.86/2.00  fd_cond                                 1
% 11.86/2.00  fd_pseudo_cond                          3
% 11.86/2.00  AC symbols                              0
% 11.86/2.00  
% 11.86/2.00  ------ Schedule dynamic 5 is on 
% 11.86/2.00  
% 11.86/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ 
% 11.86/2.00  Current options:
% 11.86/2.00  ------ 
% 11.86/2.00  
% 11.86/2.00  ------ Input Options
% 11.86/2.00  
% 11.86/2.00  --out_options                           all
% 11.86/2.00  --tptp_safe_out                         true
% 11.86/2.00  --problem_path                          ""
% 11.86/2.00  --include_path                          ""
% 11.86/2.00  --clausifier                            res/vclausify_rel
% 11.86/2.00  --clausifier_options                    ""
% 11.86/2.00  --stdin                                 false
% 11.86/2.00  --stats_out                             all
% 11.86/2.00  
% 11.86/2.00  ------ General Options
% 11.86/2.00  
% 11.86/2.00  --fof                                   false
% 11.86/2.00  --time_out_real                         305.
% 11.86/2.00  --time_out_virtual                      -1.
% 11.86/2.00  --symbol_type_check                     false
% 11.86/2.00  --clausify_out                          false
% 11.86/2.00  --sig_cnt_out                           false
% 11.86/2.00  --trig_cnt_out                          false
% 11.86/2.00  --trig_cnt_out_tolerance                1.
% 11.86/2.00  --trig_cnt_out_sk_spl                   false
% 11.86/2.00  --abstr_cl_out                          false
% 11.86/2.00  
% 11.86/2.00  ------ Global Options
% 11.86/2.00  
% 11.86/2.00  --schedule                              default
% 11.86/2.00  --add_important_lit                     false
% 11.86/2.00  --prop_solver_per_cl                    1000
% 11.86/2.00  --min_unsat_core                        false
% 11.86/2.00  --soft_assumptions                      false
% 11.86/2.00  --soft_lemma_size                       3
% 11.86/2.00  --prop_impl_unit_size                   0
% 11.86/2.00  --prop_impl_unit                        []
% 11.86/2.00  --share_sel_clauses                     true
% 11.86/2.00  --reset_solvers                         false
% 11.86/2.00  --bc_imp_inh                            [conj_cone]
% 11.86/2.00  --conj_cone_tolerance                   3.
% 11.86/2.00  --extra_neg_conj                        none
% 11.86/2.00  --large_theory_mode                     true
% 11.86/2.00  --prolific_symb_bound                   200
% 11.86/2.00  --lt_threshold                          2000
% 11.86/2.00  --clause_weak_htbl                      true
% 11.86/2.00  --gc_record_bc_elim                     false
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing Options
% 11.86/2.00  
% 11.86/2.00  --preprocessing_flag                    true
% 11.86/2.00  --time_out_prep_mult                    0.1
% 11.86/2.00  --splitting_mode                        input
% 11.86/2.00  --splitting_grd                         true
% 11.86/2.00  --splitting_cvd                         false
% 11.86/2.00  --splitting_cvd_svl                     false
% 11.86/2.00  --splitting_nvd                         32
% 11.86/2.00  --sub_typing                            true
% 11.86/2.00  --prep_gs_sim                           true
% 11.86/2.00  --prep_unflatten                        true
% 11.86/2.00  --prep_res_sim                          true
% 11.86/2.00  --prep_upred                            true
% 11.86/2.00  --prep_sem_filter                       exhaustive
% 11.86/2.00  --prep_sem_filter_out                   false
% 11.86/2.00  --pred_elim                             true
% 11.86/2.00  --res_sim_input                         true
% 11.86/2.00  --eq_ax_congr_red                       true
% 11.86/2.00  --pure_diseq_elim                       true
% 11.86/2.00  --brand_transform                       false
% 11.86/2.00  --non_eq_to_eq                          false
% 11.86/2.00  --prep_def_merge                        true
% 11.86/2.00  --prep_def_merge_prop_impl              false
% 11.86/2.00  --prep_def_merge_mbd                    true
% 11.86/2.00  --prep_def_merge_tr_red                 false
% 11.86/2.00  --prep_def_merge_tr_cl                  false
% 11.86/2.00  --smt_preprocessing                     true
% 11.86/2.00  --smt_ac_axioms                         fast
% 11.86/2.00  --preprocessed_out                      false
% 11.86/2.00  --preprocessed_stats                    false
% 11.86/2.00  
% 11.86/2.00  ------ Abstraction refinement Options
% 11.86/2.00  
% 11.86/2.00  --abstr_ref                             []
% 11.86/2.00  --abstr_ref_prep                        false
% 11.86/2.00  --abstr_ref_until_sat                   false
% 11.86/2.00  --abstr_ref_sig_restrict                funpre
% 11.86/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.86/2.00  --abstr_ref_under                       []
% 11.86/2.00  
% 11.86/2.00  ------ SAT Options
% 11.86/2.00  
% 11.86/2.00  --sat_mode                              false
% 11.86/2.00  --sat_fm_restart_options                ""
% 11.86/2.00  --sat_gr_def                            false
% 11.86/2.00  --sat_epr_types                         true
% 11.86/2.00  --sat_non_cyclic_types                  false
% 11.86/2.00  --sat_finite_models                     false
% 11.86/2.00  --sat_fm_lemmas                         false
% 11.86/2.00  --sat_fm_prep                           false
% 11.86/2.00  --sat_fm_uc_incr                        true
% 11.86/2.00  --sat_out_model                         small
% 11.86/2.00  --sat_out_clauses                       false
% 11.86/2.00  
% 11.86/2.00  ------ QBF Options
% 11.86/2.00  
% 11.86/2.00  --qbf_mode                              false
% 11.86/2.00  --qbf_elim_univ                         false
% 11.86/2.00  --qbf_dom_inst                          none
% 11.86/2.00  --qbf_dom_pre_inst                      false
% 11.86/2.00  --qbf_sk_in                             false
% 11.86/2.00  --qbf_pred_elim                         true
% 11.86/2.00  --qbf_split                             512
% 11.86/2.00  
% 11.86/2.00  ------ BMC1 Options
% 11.86/2.00  
% 11.86/2.00  --bmc1_incremental                      false
% 11.86/2.00  --bmc1_axioms                           reachable_all
% 11.86/2.00  --bmc1_min_bound                        0
% 11.86/2.00  --bmc1_max_bound                        -1
% 11.86/2.00  --bmc1_max_bound_default                -1
% 11.86/2.00  --bmc1_symbol_reachability              true
% 11.86/2.00  --bmc1_property_lemmas                  false
% 11.86/2.00  --bmc1_k_induction                      false
% 11.86/2.00  --bmc1_non_equiv_states                 false
% 11.86/2.00  --bmc1_deadlock                         false
% 11.86/2.00  --bmc1_ucm                              false
% 11.86/2.00  --bmc1_add_unsat_core                   none
% 11.86/2.00  --bmc1_unsat_core_children              false
% 11.86/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.86/2.00  --bmc1_out_stat                         full
% 11.86/2.00  --bmc1_ground_init                      false
% 11.86/2.00  --bmc1_pre_inst_next_state              false
% 11.86/2.00  --bmc1_pre_inst_state                   false
% 11.86/2.00  --bmc1_pre_inst_reach_state             false
% 11.86/2.00  --bmc1_out_unsat_core                   false
% 11.86/2.00  --bmc1_aig_witness_out                  false
% 11.86/2.00  --bmc1_verbose                          false
% 11.86/2.00  --bmc1_dump_clauses_tptp                false
% 11.86/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.86/2.00  --bmc1_dump_file                        -
% 11.86/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.86/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.86/2.00  --bmc1_ucm_extend_mode                  1
% 11.86/2.00  --bmc1_ucm_init_mode                    2
% 11.86/2.00  --bmc1_ucm_cone_mode                    none
% 11.86/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.86/2.00  --bmc1_ucm_relax_model                  4
% 11.86/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.86/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.86/2.00  --bmc1_ucm_layered_model                none
% 11.86/2.00  --bmc1_ucm_max_lemma_size               10
% 11.86/2.00  
% 11.86/2.00  ------ AIG Options
% 11.86/2.00  
% 11.86/2.00  --aig_mode                              false
% 11.86/2.00  
% 11.86/2.00  ------ Instantiation Options
% 11.86/2.00  
% 11.86/2.00  --instantiation_flag                    true
% 11.86/2.00  --inst_sos_flag                         true
% 11.86/2.00  --inst_sos_phase                        true
% 11.86/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel_side                     none
% 11.86/2.00  --inst_solver_per_active                1400
% 11.86/2.00  --inst_solver_calls_frac                1.
% 11.86/2.00  --inst_passive_queue_type               priority_queues
% 11.86/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.86/2.00  --inst_passive_queues_freq              [25;2]
% 11.86/2.00  --inst_dismatching                      true
% 11.86/2.00  --inst_eager_unprocessed_to_passive     true
% 11.86/2.00  --inst_prop_sim_given                   true
% 11.86/2.00  --inst_prop_sim_new                     false
% 11.86/2.00  --inst_subs_new                         false
% 11.86/2.00  --inst_eq_res_simp                      false
% 11.86/2.00  --inst_subs_given                       false
% 11.86/2.00  --inst_orphan_elimination               true
% 11.86/2.00  --inst_learning_loop_flag               true
% 11.86/2.00  --inst_learning_start                   3000
% 11.86/2.00  --inst_learning_factor                  2
% 11.86/2.00  --inst_start_prop_sim_after_learn       3
% 11.86/2.00  --inst_sel_renew                        solver
% 11.86/2.00  --inst_lit_activity_flag                true
% 11.86/2.00  --inst_restr_to_given                   false
% 11.86/2.00  --inst_activity_threshold               500
% 11.86/2.00  --inst_out_proof                        true
% 11.86/2.00  
% 11.86/2.00  ------ Resolution Options
% 11.86/2.00  
% 11.86/2.00  --resolution_flag                       false
% 11.86/2.00  --res_lit_sel                           adaptive
% 11.86/2.00  --res_lit_sel_side                      none
% 11.86/2.00  --res_ordering                          kbo
% 11.86/2.00  --res_to_prop_solver                    active
% 11.86/2.00  --res_prop_simpl_new                    false
% 11.86/2.00  --res_prop_simpl_given                  true
% 11.86/2.00  --res_passive_queue_type                priority_queues
% 11.86/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.86/2.00  --res_passive_queues_freq               [15;5]
% 11.86/2.00  --res_forward_subs                      full
% 11.86/2.00  --res_backward_subs                     full
% 11.86/2.00  --res_forward_subs_resolution           true
% 11.86/2.00  --res_backward_subs_resolution          true
% 11.86/2.00  --res_orphan_elimination                true
% 11.86/2.00  --res_time_limit                        2.
% 11.86/2.00  --res_out_proof                         true
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Options
% 11.86/2.00  
% 11.86/2.00  --superposition_flag                    true
% 11.86/2.00  --sup_passive_queue_type                priority_queues
% 11.86/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.86/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.86/2.00  --demod_completeness_check              fast
% 11.86/2.00  --demod_use_ground                      true
% 11.86/2.00  --sup_to_prop_solver                    passive
% 11.86/2.00  --sup_prop_simpl_new                    true
% 11.86/2.00  --sup_prop_simpl_given                  true
% 11.86/2.00  --sup_fun_splitting                     true
% 11.86/2.00  --sup_smt_interval                      50000
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Simplification Setup
% 11.86/2.00  
% 11.86/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.86/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.86/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_immed_triv                        [TrivRules]
% 11.86/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_bw_main                     []
% 11.86/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.86/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_input_bw                          []
% 11.86/2.00  
% 11.86/2.00  ------ Combination Options
% 11.86/2.00  
% 11.86/2.00  --comb_res_mult                         3
% 11.86/2.00  --comb_sup_mult                         2
% 11.86/2.00  --comb_inst_mult                        10
% 11.86/2.00  
% 11.86/2.00  ------ Debug Options
% 11.86/2.00  
% 11.86/2.00  --dbg_backtrace                         false
% 11.86/2.00  --dbg_dump_prop_clauses                 false
% 11.86/2.00  --dbg_dump_prop_clauses_file            -
% 11.86/2.00  --dbg_out_stat                          false
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  % SZS status Theorem for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  fof(f15,axiom,(
% 11.86/2.00    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f99,plain,(
% 11.86/2.00    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f15])).
% 11.86/2.00  
% 11.86/2.00  fof(f13,axiom,(
% 11.86/2.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f42,plain,(
% 11.86/2.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 11.86/2.00    inference(ennf_transformation,[],[f13])).
% 11.86/2.00  
% 11.86/2.00  fof(f96,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f42])).
% 11.86/2.00  
% 11.86/2.00  fof(f3,axiom,(
% 11.86/2.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f86,plain,(
% 11.86/2.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.86/2.00    inference(cnf_transformation,[],[f3])).
% 11.86/2.00  
% 11.86/2.00  fof(f10,axiom,(
% 11.86/2.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f38,plain,(
% 11.86/2.00    ! [X0,X1,X2,X3] : (X1 = X2 | (~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)))),
% 11.86/2.00    inference(ennf_transformation,[],[f10])).
% 11.86/2.00  
% 11.86/2.00  fof(f39,plain,(
% 11.86/2.00    ! [X0,X1,X2,X3] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3))),
% 11.86/2.00    inference(flattening,[],[f38])).
% 11.86/2.00  
% 11.86/2.00  fof(f93,plain,(
% 11.86/2.00    ( ! [X2,X0,X3,X1] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f39])).
% 11.86/2.00  
% 11.86/2.00  fof(f2,axiom,(
% 11.86/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f69,plain,(
% 11.86/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.86/2.00    inference(nnf_transformation,[],[f2])).
% 11.86/2.00  
% 11.86/2.00  fof(f70,plain,(
% 11.86/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.86/2.00    inference(flattening,[],[f69])).
% 11.86/2.00  
% 11.86/2.00  fof(f84,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.86/2.00    inference(cnf_transformation,[],[f70])).
% 11.86/2.00  
% 11.86/2.00  fof(f130,plain,(
% 11.86/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.86/2.00    inference(equality_resolution,[],[f84])).
% 11.86/2.00  
% 11.86/2.00  fof(f6,axiom,(
% 11.86/2.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f89,plain,(
% 11.86/2.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.86/2.00    inference(cnf_transformation,[],[f6])).
% 11.86/2.00  
% 11.86/2.00  fof(f11,axiom,(
% 11.86/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f40,plain,(
% 11.86/2.00    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 11.86/2.00    inference(ennf_transformation,[],[f11])).
% 11.86/2.00  
% 11.86/2.00  fof(f94,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f40])).
% 11.86/2.00  
% 11.86/2.00  fof(f14,axiom,(
% 11.86/2.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f71,plain,(
% 11.86/2.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.86/2.00    inference(nnf_transformation,[],[f14])).
% 11.86/2.00  
% 11.86/2.00  fof(f97,plain,(
% 11.86/2.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f71])).
% 11.86/2.00  
% 11.86/2.00  fof(f132,plain,(
% 11.86/2.00    ( ! [X1] : (k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1)) )),
% 11.86/2.00    inference(equality_resolution,[],[f97])).
% 11.86/2.00  
% 11.86/2.00  fof(f5,axiom,(
% 11.86/2.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f88,plain,(
% 11.86/2.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f5])).
% 11.86/2.00  
% 11.86/2.00  fof(f7,axiom,(
% 11.86/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f90,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f7])).
% 11.86/2.00  
% 11.86/2.00  fof(f129,plain,(
% 11.86/2.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 11.86/2.00    inference(definition_unfolding,[],[f88,f90])).
% 11.86/2.00  
% 11.86/2.00  fof(f1,axiom,(
% 11.86/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f34,plain,(
% 11.86/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f1])).
% 11.86/2.00  
% 11.86/2.00  fof(f65,plain,(
% 11.86/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.86/2.00    inference(nnf_transformation,[],[f34])).
% 11.86/2.00  
% 11.86/2.00  fof(f66,plain,(
% 11.86/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.86/2.00    inference(rectify,[],[f65])).
% 11.86/2.00  
% 11.86/2.00  fof(f67,plain,(
% 11.86/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f68,plain,(
% 11.86/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.86/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f66,f67])).
% 11.86/2.00  
% 11.86/2.00  fof(f80,plain,(
% 11.86/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f68])).
% 11.86/2.00  
% 11.86/2.00  fof(f16,axiom,(
% 11.86/2.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f43,plain,(
% 11.86/2.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f16])).
% 11.86/2.00  
% 11.86/2.00  fof(f72,plain,(
% 11.86/2.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.86/2.00    inference(nnf_transformation,[],[f43])).
% 11.86/2.00  
% 11.86/2.00  fof(f101,plain,(
% 11.86/2.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f72])).
% 11.86/2.00  
% 11.86/2.00  fof(f18,axiom,(
% 11.86/2.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f105,plain,(
% 11.86/2.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f18])).
% 11.86/2.00  
% 11.86/2.00  fof(f21,axiom,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f48,plain,(
% 11.86/2.00    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f21])).
% 11.86/2.00  
% 11.86/2.00  fof(f108,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f48])).
% 11.86/2.00  
% 11.86/2.00  fof(f17,axiom,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f44,plain,(
% 11.86/2.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f17])).
% 11.86/2.00  
% 11.86/2.00  fof(f104,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f44])).
% 11.86/2.00  
% 11.86/2.00  fof(f22,axiom,(
% 11.86/2.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f109,plain,(
% 11.86/2.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f22])).
% 11.86/2.00  
% 11.86/2.00  fof(f19,axiom,(
% 11.86/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f45,plain,(
% 11.86/2.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.86/2.00    inference(ennf_transformation,[],[f19])).
% 11.86/2.00  
% 11.86/2.00  fof(f46,plain,(
% 11.86/2.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.86/2.00    inference(flattening,[],[f45])).
% 11.86/2.00  
% 11.86/2.00  fof(f106,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f46])).
% 11.86/2.00  
% 11.86/2.00  fof(f20,axiom,(
% 11.86/2.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f47,plain,(
% 11.86/2.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f20])).
% 11.86/2.00  
% 11.86/2.00  fof(f107,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f47])).
% 11.86/2.00  
% 11.86/2.00  fof(f32,conjecture,(
% 11.86/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f33,negated_conjecture,(
% 11.86/2.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 11.86/2.00    inference(negated_conjecture,[],[f32])).
% 11.86/2.00  
% 11.86/2.00  fof(f63,plain,(
% 11.86/2.00    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f33])).
% 11.86/2.00  
% 11.86/2.00  fof(f64,plain,(
% 11.86/2.00    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f63])).
% 11.86/2.00  
% 11.86/2.00  fof(f73,plain,(
% 11.86/2.00    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.86/2.00    inference(nnf_transformation,[],[f64])).
% 11.86/2.00  
% 11.86/2.00  fof(f74,plain,(
% 11.86/2.00    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f73])).
% 11.86/2.00  
% 11.86/2.00  fof(f75,plain,(
% 11.86/2.00    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.86/2.00    inference(rectify,[],[f74])).
% 11.86/2.00  
% 11.86/2.00  fof(f78,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK4) & r1_tarski(sK4,X2) & v3_pre_topc(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f77,plain,(
% 11.86/2.00    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK2,k1_tops_1(X0,sK3))) & (? [X4] : (r2_hidden(sK2,X4) & r1_tarski(X4,sK3) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK2,k1_tops_1(X0,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f76,plain,(
% 11.86/2.00    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X1,k1_tops_1(sK1,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(X1,k1_tops_1(sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f79,plain,(
% 11.86/2.00    ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(sK2,k1_tops_1(sK1,sK3))) & ((r2_hidden(sK2,sK4) & r1_tarski(sK4,sK3) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(sK2,k1_tops_1(sK1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 11.86/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f75,f78,f77,f76])).
% 11.86/2.00  
% 11.86/2.00  fof(f123,plain,(
% 11.86/2.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.86/2.00    inference(cnf_transformation,[],[f79])).
% 11.86/2.00  
% 11.86/2.00  fof(f25,axiom,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f52,plain,(
% 11.86/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f25])).
% 11.86/2.00  
% 11.86/2.00  fof(f112,plain,(
% 11.86/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f52])).
% 11.86/2.00  
% 11.86/2.00  fof(f24,axiom,(
% 11.86/2.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f51,plain,(
% 11.86/2.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f24])).
% 11.86/2.00  
% 11.86/2.00  fof(f111,plain,(
% 11.86/2.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f51])).
% 11.86/2.00  
% 11.86/2.00  fof(f121,plain,(
% 11.86/2.00    l1_pre_topc(sK1)),
% 11.86/2.00    inference(cnf_transformation,[],[f79])).
% 11.86/2.00  
% 11.86/2.00  fof(f122,plain,(
% 11.86/2.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 11.86/2.00    inference(cnf_transformation,[],[f79])).
% 11.86/2.00  
% 11.86/2.00  fof(f30,axiom,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f60,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f30])).
% 11.86/2.00  
% 11.86/2.00  fof(f118,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f60])).
% 11.86/2.00  
% 11.86/2.00  fof(f127,plain,(
% 11.86/2.00    ( ! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK2,k1_tops_1(sK1,sK3))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f79])).
% 11.86/2.00  
% 11.86/2.00  fof(f29,axiom,(
% 11.86/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f58,plain,(
% 11.86/2.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f29])).
% 11.86/2.00  
% 11.86/2.00  fof(f59,plain,(
% 11.86/2.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f58])).
% 11.86/2.00  
% 11.86/2.00  fof(f117,plain,(
% 11.86/2.00    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f59])).
% 11.86/2.00  
% 11.86/2.00  fof(f120,plain,(
% 11.86/2.00    v2_pre_topc(sK1)),
% 11.86/2.00    inference(cnf_transformation,[],[f79])).
% 11.86/2.00  
% 11.86/2.00  fof(f28,axiom,(
% 11.86/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f56,plain,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f28])).
% 11.86/2.00  
% 11.86/2.00  fof(f57,plain,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f56])).
% 11.86/2.00  
% 11.86/2.00  fof(f116,plain,(
% 11.86/2.00    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f57])).
% 11.86/2.00  
% 11.86/2.00  fof(f27,axiom,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f55,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f27])).
% 11.86/2.00  
% 11.86/2.00  fof(f115,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f55])).
% 11.86/2.00  
% 11.86/2.00  fof(f26,axiom,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f53,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0))) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f26])).
% 11.86/2.00  
% 11.86/2.00  fof(f54,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0)) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f53])).
% 11.86/2.00  
% 11.86/2.00  fof(f113,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f54])).
% 11.86/2.00  
% 11.86/2.00  fof(f124,plain,(
% 11.86/2.00    v3_pre_topc(sK4,sK1) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.86/2.00    inference(cnf_transformation,[],[f79])).
% 11.86/2.00  
% 11.86/2.00  fof(f31,axiom,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f61,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f31])).
% 11.86/2.00  
% 11.86/2.00  fof(f62,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f61])).
% 11.86/2.00  
% 11.86/2.00  fof(f119,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f62])).
% 11.86/2.00  
% 11.86/2.00  fof(f126,plain,(
% 11.86/2.00    r2_hidden(sK2,sK4) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.86/2.00    inference(cnf_transformation,[],[f79])).
% 11.86/2.00  
% 11.86/2.00  fof(f125,plain,(
% 11.86/2.00    r1_tarski(sK4,sK3) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.86/2.00    inference(cnf_transformation,[],[f79])).
% 11.86/2.00  
% 11.86/2.00  cnf(c_18,plain,
% 11.86/2.00      ( r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1607,plain,
% 11.86/2.00      ( r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_15,plain,
% 11.86/2.00      ( r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1608,plain,
% 11.86/2.00      ( r1_xboole_0(k1_tarski(X0),X1) = iProver_top
% 11.86/2.00      | r2_hidden(X0,X1) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_6,plain,
% 11.86/2.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12,plain,
% 11.86/2.00      ( ~ r1_xboole_0(X0,X1)
% 11.86/2.00      | ~ r1_xboole_0(X2,X3)
% 11.86/2.00      | X2 = X1
% 11.86/2.00      | k2_xboole_0(X2,X0) != k2_xboole_0(X3,X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1611,plain,
% 11.86/2.00      ( X0 = X1
% 11.86/2.00      | k2_xboole_0(X0,X2) != k2_xboole_0(X3,X1)
% 11.86/2.00      | r1_xboole_0(X2,X1) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0,X3) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_6251,plain,
% 11.86/2.00      ( X0 = X1
% 11.86/2.00      | k2_xboole_0(X2,X0) != X1
% 11.86/2.00      | r1_xboole_0(X1,X2) != iProver_top
% 11.86/2.00      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_6,c_1611]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4,plain,
% 11.86/2.00      ( r1_tarski(X0,X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f130]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1615,plain,
% 11.86/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_9,plain,
% 11.86/2.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_13,plain,
% 11.86/2.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 11.86/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1610,plain,
% 11.86/2.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 11.86/2.00      | r1_tarski(X0,X2) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_3669,plain,
% 11.86/2.00      ( r1_xboole_0(X0,X1) = iProver_top
% 11.86/2.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_9,c_1610]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_3829,plain,
% 11.86/2.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_1615,c_3669]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_6756,plain,
% 11.86/2.00      ( r1_xboole_0(X1,X2) != iProver_top
% 11.86/2.00      | k2_xboole_0(X2,X0) != X1
% 11.86/2.00      | X0 = X1 ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_6251,c_3829]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_6757,plain,
% 11.86/2.00      ( X0 = X1
% 11.86/2.00      | k2_xboole_0(X2,X0) != X1
% 11.86/2.00      | r1_xboole_0(X1,X2) != iProver_top ),
% 11.86/2.00      inference(renaming,[status(thm)],[c_6756]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_6760,plain,
% 11.86/2.00      ( X0 != X1 | k1_xboole_0 = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_6,c_6757]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_6769,plain,
% 11.86/2.00      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 11.86/2.00      inference(equality_resolution,[status(thm)],[c_6760]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_9065,plain,
% 11.86/2.00      ( k1_tarski(X0) = k1_xboole_0
% 11.86/2.00      | r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_1608,c_6769]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_17,plain,
% 11.86/2.00      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f132]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_8,plain,
% 11.86/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f129]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1621,plain,
% 11.86/2.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.86/2.00      inference(light_normalisation,[status(thm)],[c_8,c_9]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1622,plain,
% 11.86/2.00      ( k1_tarski(X0) != k1_xboole_0 ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_17,c_1621]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_11095,plain,
% 11.86/2.00      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_9065,c_1622]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2,plain,
% 11.86/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.86/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1617,plain,
% 11.86/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.86/2.00      | r2_hidden(X0,X2) = iProver_top
% 11.86/2.00      | r1_tarski(X1,X2) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_11101,plain,
% 11.86/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.86/2.00      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_11095,c_1617]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_11940,plain,
% 11.86/2.00      ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_1607,c_11101]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_21,plain,
% 11.86/2.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f101]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1604,plain,
% 11.86/2.00      ( m1_subset_1(X0,X1) = iProver_top
% 11.86/2.00      | r2_hidden(X0,X1) != iProver_top
% 11.86/2.00      | v1_xboole_0(X1) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_11946,plain,
% 11.86/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 11.86/2.00      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_11940,c_1604]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_24,plain,
% 11.86/2.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_99,plain,
% 11.86/2.00      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12040,plain,
% 11.86/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_11946,c_99]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_27,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.86/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.86/2.00      | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f108]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1598,plain,
% 11.86/2.00      ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
% 11.86/2.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12053,plain,
% 11.86/2.00      ( k4_subset_1(X0,k3_subset_1(X0,X1),X0) = k3_subset_1(X0,k7_subset_1(X0,X1,X0))
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_12040,c_1598]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_46535,plain,
% 11.86/2.00      ( k4_subset_1(X0,k3_subset_1(X0,X0),X0) = k3_subset_1(X0,k7_subset_1(X0,X0,X0)) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_12040,c_12053]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_23,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.86/2.00      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f104]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1602,plain,
% 11.86/2.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12049,plain,
% 11.86/2.00      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_12040,c_1602]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12092,plain,
% 11.86/2.00      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 11.86/2.00      inference(light_normalisation,[status(thm)],[c_12049,c_1621]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_28,plain,
% 11.86/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f109]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1597,plain,
% 11.86/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_25,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.86/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.86/2.00      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 11.86/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1600,plain,
% 11.86/2.00      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.86/2.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12052,plain,
% 11.86/2.00      ( k4_subset_1(X0,X1,X0) = k2_xboole_0(X1,X0)
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_12040,c_1600]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_23355,plain,
% 11.86/2.00      ( k4_subset_1(X0,k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_1597,c_12052]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_46539,plain,
% 11.86/2.00      ( k3_subset_1(X0,k7_subset_1(X0,X0,X0)) = k2_xboole_0(k1_xboole_0,X0) ),
% 11.86/2.00      inference(light_normalisation,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_46535,c_12092,c_23355]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_26,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.86/2.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.86/2.00      inference(cnf_transformation,[],[f107]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1599,plain,
% 11.86/2.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12048,plain,
% 11.86/2.00      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_12040,c_1599]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_46540,plain,
% 11.86/2.00      ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(k1_xboole_0,X0) ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_46539,c_12048]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4818,plain,
% 11.86/2.00      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_1597,c_1602]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4822,plain,
% 11.86/2.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 11.86/2.00      inference(light_normalisation,[status(thm)],[c_4818,c_9]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_46541,plain,
% 11.86/2.00      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.86/2.00      inference(light_normalisation,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_46540,c_1621,c_4822]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_43,negated_conjecture,
% 11.86/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f123]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1593,plain,
% 11.86/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_31,plain,
% 11.86/2.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f112]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_30,plain,
% 11.86/2.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f111]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_478,plain,
% 11.86/2.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.86/2.00      inference(resolution,[status(thm)],[c_31,c_30]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_45,negated_conjecture,
% 11.86/2.00      ( l1_pre_topc(sK1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f121]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_538,plain,
% 11.86/2.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_478,c_45]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_539,plain,
% 11.86/2.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_538]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1623,plain,
% 11.86/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.86/2.00      inference(light_normalisation,[status(thm)],[c_1593,c_539]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_44,negated_conjecture,
% 11.86/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.86/2.00      inference(cnf_transformation,[],[f122]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_49,plain,
% 11.86/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_37,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.86/2.00      | ~ l1_pre_topc(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f118]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_561,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.86/2.00      | sK1 != X1 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_37,c_45]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_562,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_561]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1722,plain,
% 11.86/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_562]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1723,plain,
% 11.86/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.86/2.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_1722]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_39,negated_conjecture,
% 11.86/2.00      ( ~ v3_pre_topc(X0,sK1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ r2_hidden(sK2,X0)
% 11.86/2.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | ~ r1_tarski(X0,sK3) ),
% 11.86/2.00      inference(cnf_transformation,[],[f127]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_36,plain,
% 11.86/2.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.86/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.86/2.00      | ~ v2_pre_topc(X0)
% 11.86/2.00      | ~ l1_pre_topc(X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f117]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_46,negated_conjecture,
% 11.86/2.00      ( v2_pre_topc(sK1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f120]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_492,plain,
% 11.86/2.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.86/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.86/2.00      | ~ l1_pre_topc(X0)
% 11.86/2.00      | sK1 != X0 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_36,c_46]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_493,plain,
% 11.86/2.00      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ l1_pre_topc(sK1) ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_492]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_497,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_493,c_45]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_498,plain,
% 11.86/2.00      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.86/2.00      inference(renaming,[status(thm)],[c_497]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_686,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ r2_hidden(sK2,X0)
% 11.86/2.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | ~ r1_tarski(X0,sK3)
% 11.86/2.00      | k1_tops_1(sK1,X1) != X0
% 11.86/2.00      | sK1 != sK1 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_39,c_498]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_687,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 11.86/2.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_686]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_35,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f116]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_573,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | sK1 != X1 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_35,c_45]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_574,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_573]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_691,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 11.86/2.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_687,c_574]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1742,plain,
% 11.86/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_691]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1743,plain,
% 11.86/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
% 11.86/2.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_1742]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2437,plain,
% 11.86/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_1623,c_49,c_1723,c_1743]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4820,plain,
% 11.86/2.00      ( k3_subset_1(k2_struct_0(sK1),sK4) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_2437,c_1602]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_34,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1)
% 11.86/2.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f115]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_585,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 11.86/2.00      | sK1 != X1 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_34,c_45]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_586,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_585]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1588,plain,
% 11.86/2.00      ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1626,plain,
% 11.86/2.00      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 11.86/2.00      inference(light_normalisation,[status(thm)],[c_1588,c_539]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2443,plain,
% 11.86/2.00      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_2437,c_1626]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_5222,plain,
% 11.86/2.00      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_4820,c_2443]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2781,plain,
% 11.86/2.00      ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),X0),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),X0,sK4))
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_2437,c_1598]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12072,plain,
% 11.86/2.00      ( k4_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_struct_0(sK1)),sK4) = k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_12040,c_2781]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12094,plain,
% 11.86/2.00      ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_12092,c_12072]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_3479,plain,
% 11.86/2.00      ( k4_subset_1(k2_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_2437,c_1600]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4284,plain,
% 11.86/2.00      ( k4_subset_1(k2_struct_0(sK1),k1_xboole_0,sK4) = k2_xboole_0(k1_xboole_0,sK4) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_1597,c_3479]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12098,plain,
% 11.86/2.00      ( k3_subset_1(k2_struct_0(sK1),k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k2_xboole_0(k1_xboole_0,sK4) ),
% 11.86/2.00      inference(light_normalisation,[status(thm)],[c_12094,c_4284]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12099,plain,
% 11.86/2.00      ( k3_subset_1(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK4)) = k2_xboole_0(k1_xboole_0,sK4) ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_12048,c_12098]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_33,plain,
% 11.86/2.00      ( ~ v3_pre_topc(X0,X1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1)
% 11.86/2.00      | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f113]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_597,plain,
% 11.86/2.00      ( ~ v3_pre_topc(X0,X1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)
% 11.86/2.00      | sK1 != X1 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_33,c_45]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_598,plain,
% 11.86/2.00      ( ~ v3_pre_topc(X0,sK1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0) ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_597]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_42,negated_conjecture,
% 11.86/2.00      ( v3_pre_topc(sK4,sK1) | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f124]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_652,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)
% 11.86/2.00      | sK4 != X0
% 11.86/2.00      | sK1 != sK1 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_598,c_42]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_653,plain,
% 11.86/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_652]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_655,plain,
% 11.86/2.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_653,c_43]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1586,plain,
% 11.86/2.00      ( k2_pre_topc(sK1,k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4)
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1627,plain,
% 11.86/2.00      ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.86/2.00      inference(light_normalisation,[status(thm)],[c_1586,c_539]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1663,plain,
% 11.86/2.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 11.86/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_1627]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2458,plain,
% 11.86/2.00      ( k2_pre_topc(sK1,k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK4) ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_1627,c_44,c_1663,c_1722,c_1742]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_13083,plain,
% 11.86/2.00      ( k2_pre_topc(sK1,k4_xboole_0(k2_struct_0(sK1),sK4)) = k4_xboole_0(k2_struct_0(sK1),sK4) ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_12048,c_2458]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_24496,plain,
% 11.86/2.00      ( k1_tops_1(sK1,sK4) = k2_xboole_0(k1_xboole_0,sK4) ),
% 11.86/2.00      inference(light_normalisation,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_5222,c_5222,c_12099,c_13083]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_46582,plain,
% 11.86/2.00      ( k1_tops_1(sK1,sK4) = sK4 ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_46541,c_24496]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_981,plain,
% 11.86/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.86/2.00      theory(equality) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1773,plain,
% 11.86/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK2,X2) | X2 != X1 | sK2 != X0 ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_981]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_3037,plain,
% 11.86/2.00      ( r2_hidden(sK2,X0)
% 11.86/2.00      | ~ r2_hidden(sK2,sK4)
% 11.86/2.00      | X0 != sK4
% 11.86/2.00      | sK2 != sK2 ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_1773]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_7071,plain,
% 11.86/2.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 11.86/2.00      | ~ r2_hidden(sK2,sK4)
% 11.86/2.00      | k1_tops_1(sK1,sK4) != sK4
% 11.86/2.00      | sK2 != sK2 ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_3037]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1770,plain,
% 11.86/2.00      ( ~ r2_hidden(sK2,X0) | r2_hidden(sK2,X1) | ~ r1_tarski(X0,X1) ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2177,plain,
% 11.86/2.00      ( ~ r2_hidden(sK2,X0)
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | ~ r1_tarski(X0,k1_tops_1(sK1,sK3)) ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_1770]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2517,plain,
% 11.86/2.00      ( ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | ~ r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_2177]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2812,plain,
% 11.86/2.00      ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 11.86/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.86/2.00      | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_2517]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_978,plain,( X0 = X0 ),theory(equality) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2762,plain,
% 11.86/2.00      ( sK2 = sK2 ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_978]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_38,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ r1_tarski(X0,X2)
% 11.86/2.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.86/2.00      | ~ l1_pre_topc(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f119]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_543,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ r1_tarski(X0,X2)
% 11.86/2.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.86/2.00      | sK1 != X1 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_38,c_45]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_544,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ r1_tarski(X1,X0)
% 11.86/2.00      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_543]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1842,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ r1_tarski(X0,sK3)
% 11.86/2.00      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3)) ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_544]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2059,plain,
% 11.86/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.86/2.00      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3))
% 11.86/2.00      | ~ r1_tarski(sK4,sK3) ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_1842]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_40,negated_conjecture,
% 11.86/2.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r2_hidden(sK2,sK4) ),
% 11.86/2.00      inference(cnf_transformation,[],[f126]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_41,negated_conjecture,
% 11.86/2.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r1_tarski(sK4,sK3) ),
% 11.86/2.00      inference(cnf_transformation,[],[f125]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(contradiction,plain,
% 11.86/2.00      ( $false ),
% 11.86/2.00      inference(minisat,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_46582,c_7071,c_2812,c_2762,c_2059,c_1742,c_1722,c_40,
% 11.86/2.00                 c_41,c_43,c_44]) ).
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  ------                               Statistics
% 11.86/2.00  
% 11.86/2.00  ------ General
% 11.86/2.00  
% 11.86/2.00  abstr_ref_over_cycles:                  0
% 11.86/2.00  abstr_ref_under_cycles:                 0
% 11.86/2.00  gc_basic_clause_elim:                   0
% 11.86/2.00  forced_gc_time:                         0
% 11.86/2.00  parsing_time:                           0.009
% 11.86/2.00  unif_index_cands_time:                  0.
% 11.86/2.00  unif_index_add_time:                    0.
% 11.86/2.00  orderings_time:                         0.
% 11.86/2.00  out_proof_time:                         0.02
% 11.86/2.00  total_time:                             1.377
% 11.86/2.00  num_of_symbols:                         57
% 11.86/2.00  num_of_terms:                           31451
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing
% 11.86/2.00  
% 11.86/2.00  num_of_splits:                          0
% 11.86/2.00  num_of_split_atoms:                     0
% 11.86/2.00  num_of_reused_defs:                     0
% 11.86/2.00  num_eq_ax_congr_red:                    22
% 11.86/2.00  num_of_sem_filtered_clauses:            1
% 11.86/2.00  num_of_subtypes:                        0
% 11.86/2.00  monotx_restored_types:                  0
% 11.86/2.00  sat_num_of_epr_types:                   0
% 11.86/2.00  sat_num_of_non_cyclic_types:            0
% 11.86/2.00  sat_guarded_non_collapsed_types:        0
% 11.86/2.00  num_pure_diseq_elim:                    0
% 11.86/2.00  simp_replaced_by:                       0
% 11.86/2.00  res_preprocessed:                       207
% 11.86/2.00  prep_upred:                             0
% 11.86/2.00  prep_unflattend:                        12
% 11.86/2.00  smt_new_axioms:                         0
% 11.86/2.00  pred_elim_cands:                        5
% 11.86/2.00  pred_elim:                              4
% 11.86/2.00  pred_elim_cl:                           4
% 11.86/2.00  pred_elim_cycles:                       6
% 11.86/2.00  merged_defs:                            0
% 11.86/2.00  merged_defs_ncl:                        0
% 11.86/2.00  bin_hyper_res:                          0
% 11.86/2.00  prep_cycles:                            4
% 11.86/2.00  pred_elim_time:                         0.008
% 11.86/2.00  splitting_time:                         0.
% 11.86/2.00  sem_filter_time:                        0.
% 11.86/2.00  monotx_time:                            0.001
% 11.86/2.00  subtype_inf_time:                       0.
% 11.86/2.00  
% 11.86/2.00  ------ Problem properties
% 11.86/2.00  
% 11.86/2.00  clauses:                                42
% 11.86/2.00  conjectures:                            4
% 11.86/2.00  epr:                                    9
% 11.86/2.00  horn:                                   33
% 11.86/2.00  ground:                                 6
% 11.86/2.00  unary:                                  11
% 11.86/2.00  binary:                                 17
% 11.86/2.00  lits:                                   93
% 11.86/2.00  lits_eq:                                21
% 11.86/2.00  fd_pure:                                0
% 11.86/2.00  fd_pseudo:                              0
% 11.86/2.00  fd_cond:                                1
% 11.86/2.00  fd_pseudo_cond:                         3
% 11.86/2.00  ac_symbols:                             0
% 11.86/2.00  
% 11.86/2.00  ------ Propositional Solver
% 11.86/2.00  
% 11.86/2.00  prop_solver_calls:                      32
% 11.86/2.00  prop_fast_solver_calls:                 2103
% 11.86/2.00  smt_solver_calls:                       0
% 11.86/2.00  smt_fast_solver_calls:                  0
% 11.86/2.00  prop_num_of_clauses:                    18885
% 11.86/2.00  prop_preprocess_simplified:             35006
% 11.86/2.00  prop_fo_subsumed:                       37
% 11.86/2.00  prop_solver_time:                       0.
% 11.86/2.00  smt_solver_time:                        0.
% 11.86/2.00  smt_fast_solver_time:                   0.
% 11.86/2.00  prop_fast_solver_time:                  0.
% 11.86/2.00  prop_unsat_core_time:                   0.002
% 11.86/2.00  
% 11.86/2.00  ------ QBF
% 11.86/2.00  
% 11.86/2.00  qbf_q_res:                              0
% 11.86/2.00  qbf_num_tautologies:                    0
% 11.86/2.00  qbf_prep_cycles:                        0
% 11.86/2.00  
% 11.86/2.00  ------ BMC1
% 11.86/2.00  
% 11.86/2.00  bmc1_current_bound:                     -1
% 11.86/2.00  bmc1_last_solved_bound:                 -1
% 11.86/2.00  bmc1_unsat_core_size:                   -1
% 11.86/2.00  bmc1_unsat_core_parents_size:           -1
% 11.86/2.00  bmc1_merge_next_fun:                    0
% 11.86/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.86/2.00  
% 11.86/2.00  ------ Instantiation
% 11.86/2.00  
% 11.86/2.00  inst_num_of_clauses:                    4910
% 11.86/2.00  inst_num_in_passive:                    2598
% 11.86/2.00  inst_num_in_active:                     1675
% 11.86/2.00  inst_num_in_unprocessed:                637
% 11.86/2.00  inst_num_of_loops:                      2720
% 11.86/2.00  inst_num_of_learning_restarts:          0
% 11.86/2.00  inst_num_moves_active_passive:          1044
% 11.86/2.00  inst_lit_activity:                      0
% 11.86/2.00  inst_lit_activity_moves:                1
% 11.86/2.00  inst_num_tautologies:                   0
% 11.86/2.00  inst_num_prop_implied:                  0
% 11.86/2.00  inst_num_existing_simplified:           0
% 11.86/2.00  inst_num_eq_res_simplified:             0
% 11.86/2.00  inst_num_child_elim:                    0
% 11.86/2.00  inst_num_of_dismatching_blockings:      4048
% 11.86/2.00  inst_num_of_non_proper_insts:           7944
% 11.86/2.00  inst_num_of_duplicates:                 0
% 11.86/2.00  inst_inst_num_from_inst_to_res:         0
% 11.86/2.00  inst_dismatching_checking_time:         0.
% 11.86/2.00  
% 11.86/2.00  ------ Resolution
% 11.86/2.00  
% 11.86/2.00  res_num_of_clauses:                     0
% 11.86/2.00  res_num_in_passive:                     0
% 11.86/2.00  res_num_in_active:                      0
% 11.86/2.00  res_num_of_loops:                       211
% 11.86/2.00  res_forward_subset_subsumed:            429
% 11.86/2.00  res_backward_subset_subsumed:           2
% 11.86/2.00  res_forward_subsumed:                   0
% 11.86/2.00  res_backward_subsumed:                  0
% 11.86/2.00  res_forward_subsumption_resolution:     0
% 11.86/2.00  res_backward_subsumption_resolution:    0
% 11.86/2.00  res_clause_to_clause_subsumption:       5907
% 11.86/2.00  res_orphan_elimination:                 0
% 11.86/2.00  res_tautology_del:                      367
% 11.86/2.00  res_num_eq_res_simplified:              0
% 11.86/2.00  res_num_sel_changes:                    0
% 11.86/2.00  res_moves_from_active_to_pass:          0
% 11.86/2.00  
% 11.86/2.00  ------ Superposition
% 11.86/2.00  
% 11.86/2.00  sup_time_total:                         0.
% 11.86/2.00  sup_time_generating:                    0.
% 11.86/2.00  sup_time_sim_full:                      0.
% 11.86/2.00  sup_time_sim_immed:                     0.
% 11.86/2.00  
% 11.86/2.00  sup_num_of_clauses:                     1345
% 11.86/2.00  sup_num_in_active:                      423
% 11.86/2.00  sup_num_in_passive:                     922
% 11.86/2.00  sup_num_of_loops:                       543
% 11.86/2.00  sup_fw_superposition:                   1459
% 11.86/2.00  sup_bw_superposition:                   582
% 11.86/2.00  sup_immediate_simplified:               672
% 11.86/2.00  sup_given_eliminated:                   5
% 11.86/2.00  comparisons_done:                       0
% 11.86/2.00  comparisons_avoided:                    21
% 11.86/2.00  
% 11.86/2.00  ------ Simplifications
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  sim_fw_subset_subsumed:                 68
% 11.86/2.00  sim_bw_subset_subsumed:                 11
% 11.86/2.00  sim_fw_subsumed:                        260
% 11.86/2.00  sim_bw_subsumed:                        12
% 11.86/2.00  sim_fw_subsumption_res:                 0
% 11.86/2.00  sim_bw_subsumption_res:                 0
% 11.86/2.00  sim_tautology_del:                      11
% 11.86/2.00  sim_eq_tautology_del:                   173
% 11.86/2.00  sim_eq_res_simp:                        0
% 11.86/2.00  sim_fw_demodulated:                     212
% 11.86/2.00  sim_bw_demodulated:                     115
% 11.86/2.00  sim_light_normalised:                   338
% 11.86/2.00  sim_joinable_taut:                      0
% 11.86/2.00  sim_joinable_simp:                      0
% 11.86/2.00  sim_ac_normalised:                      0
% 11.86/2.00  sim_smt_subsumption:                    0
% 11.86/2.00  
%------------------------------------------------------------------------------
