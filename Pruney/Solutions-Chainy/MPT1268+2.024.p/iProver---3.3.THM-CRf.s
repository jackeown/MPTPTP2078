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
% DateTime   : Thu Dec  3 12:15:06 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  186 (2927 expanded)
%              Number of clauses        :  131 ( 838 expanded)
%              Number of leaves         :   14 ( 671 expanded)
%              Depth                    :   28
%              Number of atoms          :  631 (22590 expanded)
%              Number of equality atoms :  255 (4146 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 != X2
          & v3_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,X0)
        & r1_tarski(sK2,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,X0)
              & r1_tarski(X2,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tops_1(sK1,X0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,X0)
              | ~ r1_tarski(X3,sK1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1589,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_291,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_292,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_20])).

cnf(c_297,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_1581,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_2843,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_1581])).

cnf(c_18,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1583,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2846,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_1583])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1797,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1934,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(c_1935,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1813,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2205,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1813])).

cnf(c_2206,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2205])).

cnf(c_4154,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | v2_tops_1(sK1,sK0) = iProver_top
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2846,c_24,c_1935,c_2206])).

cnf(c_4155,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4154])).

cnf(c_5096,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_4155])).

cnf(c_12,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_327,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_328,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_1731,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1732,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1731])).

cnf(c_1582,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2365,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_1581])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_342,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_343,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_1578,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_2844,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_1578])).

cnf(c_5586,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_2844])).

cnf(c_5891,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,sK1)) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5586,c_24,c_1935,c_2206])).

cnf(c_5892,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5891])).

cnf(c_1591,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5900,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5892,c_1591])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_57,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_1734,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_1735,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1734])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1863,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2037,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2038,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2041,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2038])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_312,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_313,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_1580,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_2551,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_1580])).

cnf(c_1104,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1858,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | k1_tops_1(sK0,sK1) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_2120,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | k1_tops_1(sK0,sK1) != X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1858])).

cnf(c_2645,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2120])).

cnf(c_2646,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2645])).

cnf(c_4164,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2365,c_4155])).

cnf(c_1978,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0)
    | r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5807,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
    | r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1978])).

cnf(c_5808,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5807])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1590,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3073,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1590,c_1591])).

cnf(c_1594,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1593,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2227,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1594,c_1593])).

cnf(c_3099,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_1590])).

cnf(c_1595,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3897,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_1595])).

cnf(c_5846,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3073,c_3897])).

cnf(c_6152,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5900,c_24,c_57,c_1735,c_2037,c_2038,c_2041,c_2551,c_2646,c_4164,c_5808,c_5846,c_5892])).

cnf(c_6153,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6152])).

cnf(c_6160,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2365,c_6153])).

cnf(c_6781,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6160,c_24,c_1735])).

cnf(c_6792,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6781,c_3897])).

cnf(c_7090,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5096,c_24,c_1732,c_1735,c_2551,c_4164])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1586,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7095,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7090,c_1586])).

cnf(c_7208,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7095,c_6153])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1584,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2002,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1584,c_1578])).

cnf(c_392,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1))
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_343])).

cnf(c_393,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_17])).

cnf(c_398,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_399,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_3612,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2002,c_399])).

cnf(c_3622,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_3612])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3792,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3622,c_29])).

cnf(c_3793,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3792])).

cnf(c_3800,plain,
    ( k4_xboole_0(sK2,k1_tops_1(sK0,sK1)) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3793,c_1593])).

cnf(c_3821,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k4_xboole_0(sK2,k1_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3800])).

cnf(c_5084,plain,
    ( k4_xboole_0(sK2,k1_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3800,c_19,c_24,c_1731,c_1735,c_2551,c_3821,c_4164])).

cnf(c_1592,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5088,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5084,c_1592])).

cnf(c_5619,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5088,c_1591])).

cnf(c_7720,plain,
    ( r1_tarski(sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7208,c_24,c_1735,c_5619,c_6160])).

cnf(c_7731,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7720,c_3897])).

cnf(c_1577,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_1889,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1584,c_1577])).

cnf(c_2901,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_1595])).

cnf(c_1897,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1889])).

cnf(c_3621,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1584,c_3612])).

cnf(c_3765,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3621,c_1594])).

cnf(c_3768,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3765,c_1595])).

cnf(c_3789,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3768])).

cnf(c_5261,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2901,c_19,c_24,c_1731,c_1735,c_1897,c_2551,c_3789,c_4164])).

cnf(c_1579,plain,
    ( k1_tops_1(sK0,X0) != k1_xboole_0
    | v2_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_5284,plain,
    ( sK2 != k1_xboole_0
    | v2_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5261,c_1579])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_624,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_328])).

cnf(c_625,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_627,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_19])).

cnf(c_5399,plain,
    ( sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5284,c_19,c_24,c_625,c_1735,c_2551,c_4164])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7731,c_5399])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.46/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.46/0.99  
% 2.46/0.99  ------  iProver source info
% 2.46/0.99  
% 2.46/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.46/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.46/0.99  git: non_committed_changes: false
% 2.46/0.99  git: last_make_outside_of_git: false
% 2.46/0.99  
% 2.46/0.99  ------ 
% 2.46/0.99  
% 2.46/0.99  ------ Input Options
% 2.46/0.99  
% 2.46/0.99  --out_options                           all
% 2.46/0.99  --tptp_safe_out                         true
% 2.46/0.99  --problem_path                          ""
% 2.46/0.99  --include_path                          ""
% 2.46/0.99  --clausifier                            res/vclausify_rel
% 2.46/0.99  --clausifier_options                    --mode clausify
% 2.46/0.99  --stdin                                 false
% 2.46/0.99  --stats_out                             all
% 2.46/0.99  
% 2.46/0.99  ------ General Options
% 2.46/0.99  
% 2.46/0.99  --fof                                   false
% 2.46/0.99  --time_out_real                         305.
% 2.46/0.99  --time_out_virtual                      -1.
% 2.46/0.99  --symbol_type_check                     false
% 2.46/0.99  --clausify_out                          false
% 2.46/0.99  --sig_cnt_out                           false
% 2.46/0.99  --trig_cnt_out                          false
% 2.46/0.99  --trig_cnt_out_tolerance                1.
% 2.46/0.99  --trig_cnt_out_sk_spl                   false
% 2.46/0.99  --abstr_cl_out                          false
% 2.46/0.99  
% 2.46/0.99  ------ Global Options
% 2.46/0.99  
% 2.46/0.99  --schedule                              default
% 2.46/0.99  --add_important_lit                     false
% 2.46/0.99  --prop_solver_per_cl                    1000
% 2.46/0.99  --min_unsat_core                        false
% 2.46/0.99  --soft_assumptions                      false
% 2.46/0.99  --soft_lemma_size                       3
% 2.46/0.99  --prop_impl_unit_size                   0
% 2.46/0.99  --prop_impl_unit                        []
% 2.46/0.99  --share_sel_clauses                     true
% 2.46/0.99  --reset_solvers                         false
% 2.46/0.99  --bc_imp_inh                            [conj_cone]
% 2.46/0.99  --conj_cone_tolerance                   3.
% 2.46/0.99  --extra_neg_conj                        none
% 2.46/0.99  --large_theory_mode                     true
% 2.46/0.99  --prolific_symb_bound                   200
% 2.46/0.99  --lt_threshold                          2000
% 2.46/0.99  --clause_weak_htbl                      true
% 2.46/0.99  --gc_record_bc_elim                     false
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing Options
% 2.46/0.99  
% 2.46/0.99  --preprocessing_flag                    true
% 2.46/0.99  --time_out_prep_mult                    0.1
% 2.46/0.99  --splitting_mode                        input
% 2.46/0.99  --splitting_grd                         true
% 2.46/0.99  --splitting_cvd                         false
% 2.46/0.99  --splitting_cvd_svl                     false
% 2.46/0.99  --splitting_nvd                         32
% 2.46/0.99  --sub_typing                            true
% 2.46/0.99  --prep_gs_sim                           true
% 2.46/0.99  --prep_unflatten                        true
% 2.46/0.99  --prep_res_sim                          true
% 2.46/0.99  --prep_upred                            true
% 2.46/0.99  --prep_sem_filter                       exhaustive
% 2.46/0.99  --prep_sem_filter_out                   false
% 2.46/0.99  --pred_elim                             true
% 2.46/0.99  --res_sim_input                         true
% 2.46/0.99  --eq_ax_congr_red                       true
% 2.46/0.99  --pure_diseq_elim                       true
% 2.46/0.99  --brand_transform                       false
% 2.46/0.99  --non_eq_to_eq                          false
% 2.46/0.99  --prep_def_merge                        true
% 2.46/0.99  --prep_def_merge_prop_impl              false
% 2.46/0.99  --prep_def_merge_mbd                    true
% 2.46/0.99  --prep_def_merge_tr_red                 false
% 2.46/0.99  --prep_def_merge_tr_cl                  false
% 2.46/0.99  --smt_preprocessing                     true
% 2.46/0.99  --smt_ac_axioms                         fast
% 2.46/0.99  --preprocessed_out                      false
% 2.46/0.99  --preprocessed_stats                    false
% 2.46/0.99  
% 2.46/0.99  ------ Abstraction refinement Options
% 2.46/0.99  
% 2.46/0.99  --abstr_ref                             []
% 2.46/0.99  --abstr_ref_prep                        false
% 2.46/0.99  --abstr_ref_until_sat                   false
% 2.46/0.99  --abstr_ref_sig_restrict                funpre
% 2.46/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.99  --abstr_ref_under                       []
% 2.46/0.99  
% 2.46/0.99  ------ SAT Options
% 2.46/0.99  
% 2.46/0.99  --sat_mode                              false
% 2.46/0.99  --sat_fm_restart_options                ""
% 2.46/0.99  --sat_gr_def                            false
% 2.46/0.99  --sat_epr_types                         true
% 2.46/0.99  --sat_non_cyclic_types                  false
% 2.46/0.99  --sat_finite_models                     false
% 2.46/0.99  --sat_fm_lemmas                         false
% 2.46/0.99  --sat_fm_prep                           false
% 2.46/0.99  --sat_fm_uc_incr                        true
% 2.46/0.99  --sat_out_model                         small
% 2.46/0.99  --sat_out_clauses                       false
% 2.46/0.99  
% 2.46/0.99  ------ QBF Options
% 2.46/0.99  
% 2.46/0.99  --qbf_mode                              false
% 2.46/0.99  --qbf_elim_univ                         false
% 2.46/0.99  --qbf_dom_inst                          none
% 2.46/0.99  --qbf_dom_pre_inst                      false
% 2.46/0.99  --qbf_sk_in                             false
% 2.46/0.99  --qbf_pred_elim                         true
% 2.46/0.99  --qbf_split                             512
% 2.46/0.99  
% 2.46/0.99  ------ BMC1 Options
% 2.46/0.99  
% 2.46/0.99  --bmc1_incremental                      false
% 2.46/0.99  --bmc1_axioms                           reachable_all
% 2.46/0.99  --bmc1_min_bound                        0
% 2.46/0.99  --bmc1_max_bound                        -1
% 2.46/0.99  --bmc1_max_bound_default                -1
% 2.46/0.99  --bmc1_symbol_reachability              true
% 2.46/0.99  --bmc1_property_lemmas                  false
% 2.46/0.99  --bmc1_k_induction                      false
% 2.46/0.99  --bmc1_non_equiv_states                 false
% 2.46/0.99  --bmc1_deadlock                         false
% 2.46/0.99  --bmc1_ucm                              false
% 2.46/0.99  --bmc1_add_unsat_core                   none
% 2.46/0.99  --bmc1_unsat_core_children              false
% 2.46/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.99  --bmc1_out_stat                         full
% 2.46/0.99  --bmc1_ground_init                      false
% 2.46/0.99  --bmc1_pre_inst_next_state              false
% 2.46/0.99  --bmc1_pre_inst_state                   false
% 2.46/0.99  --bmc1_pre_inst_reach_state             false
% 2.46/0.99  --bmc1_out_unsat_core                   false
% 2.46/0.99  --bmc1_aig_witness_out                  false
% 2.46/0.99  --bmc1_verbose                          false
% 2.46/0.99  --bmc1_dump_clauses_tptp                false
% 2.46/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.99  --bmc1_dump_file                        -
% 2.46/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.99  --bmc1_ucm_extend_mode                  1
% 2.46/0.99  --bmc1_ucm_init_mode                    2
% 2.46/0.99  --bmc1_ucm_cone_mode                    none
% 2.46/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.99  --bmc1_ucm_relax_model                  4
% 2.46/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.99  --bmc1_ucm_layered_model                none
% 2.46/0.99  --bmc1_ucm_max_lemma_size               10
% 2.46/0.99  
% 2.46/0.99  ------ AIG Options
% 2.46/0.99  
% 2.46/0.99  --aig_mode                              false
% 2.46/0.99  
% 2.46/0.99  ------ Instantiation Options
% 2.46/0.99  
% 2.46/0.99  --instantiation_flag                    true
% 2.46/0.99  --inst_sos_flag                         false
% 2.46/0.99  --inst_sos_phase                        true
% 2.46/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel_side                     num_symb
% 2.46/0.99  --inst_solver_per_active                1400
% 2.46/0.99  --inst_solver_calls_frac                1.
% 2.46/0.99  --inst_passive_queue_type               priority_queues
% 2.46/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.99  --inst_passive_queues_freq              [25;2]
% 2.46/0.99  --inst_dismatching                      true
% 2.46/0.99  --inst_eager_unprocessed_to_passive     true
% 2.46/0.99  --inst_prop_sim_given                   true
% 2.46/0.99  --inst_prop_sim_new                     false
% 2.46/0.99  --inst_subs_new                         false
% 2.46/1.00  --inst_eq_res_simp                      false
% 2.46/1.00  --inst_subs_given                       false
% 2.46/1.00  --inst_orphan_elimination               true
% 2.46/1.00  --inst_learning_loop_flag               true
% 2.46/1.00  --inst_learning_start                   3000
% 2.46/1.00  --inst_learning_factor                  2
% 2.46/1.00  --inst_start_prop_sim_after_learn       3
% 2.46/1.00  --inst_sel_renew                        solver
% 2.46/1.00  --inst_lit_activity_flag                true
% 2.46/1.00  --inst_restr_to_given                   false
% 2.46/1.00  --inst_activity_threshold               500
% 2.46/1.00  --inst_out_proof                        true
% 2.46/1.00  
% 2.46/1.00  ------ Resolution Options
% 2.46/1.00  
% 2.46/1.00  --resolution_flag                       true
% 2.46/1.00  --res_lit_sel                           adaptive
% 2.46/1.00  --res_lit_sel_side                      none
% 2.46/1.00  --res_ordering                          kbo
% 2.46/1.00  --res_to_prop_solver                    active
% 2.46/1.00  --res_prop_simpl_new                    false
% 2.46/1.00  --res_prop_simpl_given                  true
% 2.46/1.00  --res_passive_queue_type                priority_queues
% 2.46/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/1.00  --res_passive_queues_freq               [15;5]
% 2.46/1.00  --res_forward_subs                      full
% 2.46/1.00  --res_backward_subs                     full
% 2.46/1.00  --res_forward_subs_resolution           true
% 2.46/1.00  --res_backward_subs_resolution          true
% 2.46/1.00  --res_orphan_elimination                true
% 2.46/1.00  --res_time_limit                        2.
% 2.46/1.00  --res_out_proof                         true
% 2.46/1.00  
% 2.46/1.00  ------ Superposition Options
% 2.46/1.00  
% 2.46/1.00  --superposition_flag                    true
% 2.46/1.00  --sup_passive_queue_type                priority_queues
% 2.46/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.46/1.00  --demod_completeness_check              fast
% 2.46/1.00  --demod_use_ground                      true
% 2.46/1.00  --sup_to_prop_solver                    passive
% 2.46/1.00  --sup_prop_simpl_new                    true
% 2.46/1.00  --sup_prop_simpl_given                  true
% 2.46/1.00  --sup_fun_splitting                     false
% 2.46/1.00  --sup_smt_interval                      50000
% 2.46/1.00  
% 2.46/1.00  ------ Superposition Simplification Setup
% 2.46/1.00  
% 2.46/1.00  --sup_indices_passive                   []
% 2.46/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_full_bw                           [BwDemod]
% 2.46/1.00  --sup_immed_triv                        [TrivRules]
% 2.46/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_immed_bw_main                     []
% 2.46/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.00  
% 2.46/1.00  ------ Combination Options
% 2.46/1.00  
% 2.46/1.00  --comb_res_mult                         3
% 2.46/1.00  --comb_sup_mult                         2
% 2.46/1.00  --comb_inst_mult                        10
% 2.46/1.00  
% 2.46/1.00  ------ Debug Options
% 2.46/1.00  
% 2.46/1.00  --dbg_backtrace                         false
% 2.46/1.00  --dbg_dump_prop_clauses                 false
% 2.46/1.00  --dbg_dump_prop_clauses_file            -
% 2.46/1.00  --dbg_out_stat                          false
% 2.46/1.00  ------ Parsing...
% 2.46/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.46/1.00  ------ Proving...
% 2.46/1.00  ------ Problem Properties 
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  clauses                                 19
% 2.46/1.00  conjectures                             6
% 2.46/1.00  EPR                                     6
% 2.46/1.00  Horn                                    18
% 2.46/1.00  unary                                   3
% 2.46/1.00  binary                                  10
% 2.46/1.00  lits                                    45
% 2.46/1.00  lits eq                                 7
% 2.46/1.00  fd_pure                                 0
% 2.46/1.00  fd_pseudo                               0
% 2.46/1.00  fd_cond                                 1
% 2.46/1.00  fd_pseudo_cond                          1
% 2.46/1.00  AC symbols                              0
% 2.46/1.00  
% 2.46/1.00  ------ Schedule dynamic 5 is on 
% 2.46/1.00  
% 2.46/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  ------ 
% 2.46/1.00  Current options:
% 2.46/1.00  ------ 
% 2.46/1.00  
% 2.46/1.00  ------ Input Options
% 2.46/1.00  
% 2.46/1.00  --out_options                           all
% 2.46/1.00  --tptp_safe_out                         true
% 2.46/1.00  --problem_path                          ""
% 2.46/1.00  --include_path                          ""
% 2.46/1.00  --clausifier                            res/vclausify_rel
% 2.46/1.00  --clausifier_options                    --mode clausify
% 2.46/1.00  --stdin                                 false
% 2.46/1.00  --stats_out                             all
% 2.46/1.00  
% 2.46/1.00  ------ General Options
% 2.46/1.00  
% 2.46/1.00  --fof                                   false
% 2.46/1.00  --time_out_real                         305.
% 2.46/1.00  --time_out_virtual                      -1.
% 2.46/1.00  --symbol_type_check                     false
% 2.46/1.00  --clausify_out                          false
% 2.46/1.00  --sig_cnt_out                           false
% 2.46/1.00  --trig_cnt_out                          false
% 2.46/1.00  --trig_cnt_out_tolerance                1.
% 2.46/1.00  --trig_cnt_out_sk_spl                   false
% 2.46/1.00  --abstr_cl_out                          false
% 2.46/1.00  
% 2.46/1.00  ------ Global Options
% 2.46/1.00  
% 2.46/1.00  --schedule                              default
% 2.46/1.00  --add_important_lit                     false
% 2.46/1.00  --prop_solver_per_cl                    1000
% 2.46/1.00  --min_unsat_core                        false
% 2.46/1.00  --soft_assumptions                      false
% 2.46/1.00  --soft_lemma_size                       3
% 2.46/1.00  --prop_impl_unit_size                   0
% 2.46/1.00  --prop_impl_unit                        []
% 2.46/1.00  --share_sel_clauses                     true
% 2.46/1.00  --reset_solvers                         false
% 2.46/1.00  --bc_imp_inh                            [conj_cone]
% 2.46/1.00  --conj_cone_tolerance                   3.
% 2.46/1.00  --extra_neg_conj                        none
% 2.46/1.00  --large_theory_mode                     true
% 2.46/1.00  --prolific_symb_bound                   200
% 2.46/1.00  --lt_threshold                          2000
% 2.46/1.00  --clause_weak_htbl                      true
% 2.46/1.00  --gc_record_bc_elim                     false
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing Options
% 2.46/1.00  
% 2.46/1.00  --preprocessing_flag                    true
% 2.46/1.00  --time_out_prep_mult                    0.1
% 2.46/1.00  --splitting_mode                        input
% 2.46/1.00  --splitting_grd                         true
% 2.46/1.00  --splitting_cvd                         false
% 2.46/1.00  --splitting_cvd_svl                     false
% 2.46/1.00  --splitting_nvd                         32
% 2.46/1.00  --sub_typing                            true
% 2.46/1.00  --prep_gs_sim                           true
% 2.46/1.00  --prep_unflatten                        true
% 2.46/1.00  --prep_res_sim                          true
% 2.46/1.00  --prep_upred                            true
% 2.46/1.00  --prep_sem_filter                       exhaustive
% 2.46/1.00  --prep_sem_filter_out                   false
% 2.46/1.00  --pred_elim                             true
% 2.46/1.00  --res_sim_input                         true
% 2.46/1.00  --eq_ax_congr_red                       true
% 2.46/1.00  --pure_diseq_elim                       true
% 2.46/1.00  --brand_transform                       false
% 2.46/1.00  --non_eq_to_eq                          false
% 2.46/1.00  --prep_def_merge                        true
% 2.46/1.00  --prep_def_merge_prop_impl              false
% 2.46/1.00  --prep_def_merge_mbd                    true
% 2.46/1.00  --prep_def_merge_tr_red                 false
% 2.46/1.00  --prep_def_merge_tr_cl                  false
% 2.46/1.00  --smt_preprocessing                     true
% 2.46/1.00  --smt_ac_axioms                         fast
% 2.46/1.00  --preprocessed_out                      false
% 2.46/1.00  --preprocessed_stats                    false
% 2.46/1.00  
% 2.46/1.00  ------ Abstraction refinement Options
% 2.46/1.00  
% 2.46/1.00  --abstr_ref                             []
% 2.46/1.00  --abstr_ref_prep                        false
% 2.46/1.00  --abstr_ref_until_sat                   false
% 2.46/1.00  --abstr_ref_sig_restrict                funpre
% 2.46/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/1.00  --abstr_ref_under                       []
% 2.46/1.00  
% 2.46/1.00  ------ SAT Options
% 2.46/1.00  
% 2.46/1.00  --sat_mode                              false
% 2.46/1.00  --sat_fm_restart_options                ""
% 2.46/1.00  --sat_gr_def                            false
% 2.46/1.00  --sat_epr_types                         true
% 2.46/1.00  --sat_non_cyclic_types                  false
% 2.46/1.00  --sat_finite_models                     false
% 2.46/1.00  --sat_fm_lemmas                         false
% 2.46/1.00  --sat_fm_prep                           false
% 2.46/1.00  --sat_fm_uc_incr                        true
% 2.46/1.00  --sat_out_model                         small
% 2.46/1.00  --sat_out_clauses                       false
% 2.46/1.00  
% 2.46/1.00  ------ QBF Options
% 2.46/1.00  
% 2.46/1.00  --qbf_mode                              false
% 2.46/1.00  --qbf_elim_univ                         false
% 2.46/1.00  --qbf_dom_inst                          none
% 2.46/1.00  --qbf_dom_pre_inst                      false
% 2.46/1.00  --qbf_sk_in                             false
% 2.46/1.00  --qbf_pred_elim                         true
% 2.46/1.00  --qbf_split                             512
% 2.46/1.00  
% 2.46/1.00  ------ BMC1 Options
% 2.46/1.00  
% 2.46/1.00  --bmc1_incremental                      false
% 2.46/1.00  --bmc1_axioms                           reachable_all
% 2.46/1.00  --bmc1_min_bound                        0
% 2.46/1.00  --bmc1_max_bound                        -1
% 2.46/1.00  --bmc1_max_bound_default                -1
% 2.46/1.00  --bmc1_symbol_reachability              true
% 2.46/1.00  --bmc1_property_lemmas                  false
% 2.46/1.00  --bmc1_k_induction                      false
% 2.46/1.00  --bmc1_non_equiv_states                 false
% 2.46/1.00  --bmc1_deadlock                         false
% 2.46/1.00  --bmc1_ucm                              false
% 2.46/1.00  --bmc1_add_unsat_core                   none
% 2.46/1.00  --bmc1_unsat_core_children              false
% 2.46/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/1.00  --bmc1_out_stat                         full
% 2.46/1.00  --bmc1_ground_init                      false
% 2.46/1.00  --bmc1_pre_inst_next_state              false
% 2.46/1.00  --bmc1_pre_inst_state                   false
% 2.46/1.00  --bmc1_pre_inst_reach_state             false
% 2.46/1.00  --bmc1_out_unsat_core                   false
% 2.46/1.00  --bmc1_aig_witness_out                  false
% 2.46/1.00  --bmc1_verbose                          false
% 2.46/1.00  --bmc1_dump_clauses_tptp                false
% 2.46/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.46/1.00  --bmc1_dump_file                        -
% 2.46/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.46/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.46/1.00  --bmc1_ucm_extend_mode                  1
% 2.46/1.00  --bmc1_ucm_init_mode                    2
% 2.46/1.00  --bmc1_ucm_cone_mode                    none
% 2.46/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.46/1.00  --bmc1_ucm_relax_model                  4
% 2.46/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.46/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/1.00  --bmc1_ucm_layered_model                none
% 2.46/1.00  --bmc1_ucm_max_lemma_size               10
% 2.46/1.00  
% 2.46/1.00  ------ AIG Options
% 2.46/1.00  
% 2.46/1.00  --aig_mode                              false
% 2.46/1.00  
% 2.46/1.00  ------ Instantiation Options
% 2.46/1.00  
% 2.46/1.00  --instantiation_flag                    true
% 2.46/1.00  --inst_sos_flag                         false
% 2.46/1.00  --inst_sos_phase                        true
% 2.46/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/1.00  --inst_lit_sel_side                     none
% 2.46/1.00  --inst_solver_per_active                1400
% 2.46/1.00  --inst_solver_calls_frac                1.
% 2.46/1.00  --inst_passive_queue_type               priority_queues
% 2.46/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/1.00  --inst_passive_queues_freq              [25;2]
% 2.46/1.00  --inst_dismatching                      true
% 2.46/1.00  --inst_eager_unprocessed_to_passive     true
% 2.46/1.00  --inst_prop_sim_given                   true
% 2.46/1.00  --inst_prop_sim_new                     false
% 2.46/1.00  --inst_subs_new                         false
% 2.46/1.00  --inst_eq_res_simp                      false
% 2.46/1.00  --inst_subs_given                       false
% 2.46/1.00  --inst_orphan_elimination               true
% 2.46/1.00  --inst_learning_loop_flag               true
% 2.46/1.00  --inst_learning_start                   3000
% 2.46/1.00  --inst_learning_factor                  2
% 2.46/1.00  --inst_start_prop_sim_after_learn       3
% 2.46/1.00  --inst_sel_renew                        solver
% 2.46/1.00  --inst_lit_activity_flag                true
% 2.46/1.00  --inst_restr_to_given                   false
% 2.46/1.00  --inst_activity_threshold               500
% 2.46/1.00  --inst_out_proof                        true
% 2.46/1.00  
% 2.46/1.00  ------ Resolution Options
% 2.46/1.00  
% 2.46/1.00  --resolution_flag                       false
% 2.46/1.00  --res_lit_sel                           adaptive
% 2.46/1.00  --res_lit_sel_side                      none
% 2.46/1.00  --res_ordering                          kbo
% 2.46/1.00  --res_to_prop_solver                    active
% 2.46/1.00  --res_prop_simpl_new                    false
% 2.46/1.00  --res_prop_simpl_given                  true
% 2.46/1.00  --res_passive_queue_type                priority_queues
% 2.46/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/1.00  --res_passive_queues_freq               [15;5]
% 2.46/1.00  --res_forward_subs                      full
% 2.46/1.00  --res_backward_subs                     full
% 2.46/1.00  --res_forward_subs_resolution           true
% 2.46/1.00  --res_backward_subs_resolution          true
% 2.46/1.00  --res_orphan_elimination                true
% 2.46/1.00  --res_time_limit                        2.
% 2.46/1.00  --res_out_proof                         true
% 2.46/1.00  
% 2.46/1.00  ------ Superposition Options
% 2.46/1.00  
% 2.46/1.00  --superposition_flag                    true
% 2.46/1.00  --sup_passive_queue_type                priority_queues
% 2.46/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.46/1.00  --demod_completeness_check              fast
% 2.46/1.00  --demod_use_ground                      true
% 2.46/1.00  --sup_to_prop_solver                    passive
% 2.46/1.00  --sup_prop_simpl_new                    true
% 2.46/1.00  --sup_prop_simpl_given                  true
% 2.46/1.00  --sup_fun_splitting                     false
% 2.46/1.00  --sup_smt_interval                      50000
% 2.46/1.00  
% 2.46/1.00  ------ Superposition Simplification Setup
% 2.46/1.00  
% 2.46/1.00  --sup_indices_passive                   []
% 2.46/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_full_bw                           [BwDemod]
% 2.46/1.00  --sup_immed_triv                        [TrivRules]
% 2.46/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_immed_bw_main                     []
% 2.46/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.00  
% 2.46/1.00  ------ Combination Options
% 2.46/1.00  
% 2.46/1.00  --comb_res_mult                         3
% 2.46/1.00  --comb_sup_mult                         2
% 2.46/1.00  --comb_inst_mult                        10
% 2.46/1.00  
% 2.46/1.00  ------ Debug Options
% 2.46/1.00  
% 2.46/1.00  --dbg_backtrace                         false
% 2.46/1.00  --dbg_dump_prop_clauses                 false
% 2.46/1.00  --dbg_dump_prop_clauses_file            -
% 2.46/1.00  --dbg_out_stat                          false
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  ------ Proving...
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  % SZS status Theorem for theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  fof(f5,axiom,(
% 2.46/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f25,plain,(
% 2.46/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.46/1.00    inference(nnf_transformation,[],[f5])).
% 2.46/1.00  
% 2.46/1.00  fof(f42,plain,(
% 2.46/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f25])).
% 2.46/1.00  
% 2.46/1.00  fof(f6,axiom,(
% 2.46/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f14,plain,(
% 2.46/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.46/1.00    inference(ennf_transformation,[],[f6])).
% 2.46/1.00  
% 2.46/1.00  fof(f15,plain,(
% 2.46/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.46/1.00    inference(flattening,[],[f14])).
% 2.46/1.00  
% 2.46/1.00  fof(f43,plain,(
% 2.46/1.00    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f15])).
% 2.46/1.00  
% 2.46/1.00  fof(f10,conjecture,(
% 2.46/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f11,negated_conjecture,(
% 2.46/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.46/1.00    inference(negated_conjecture,[],[f10])).
% 2.46/1.00  
% 2.46/1.00  fof(f20,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.46/1.00    inference(ennf_transformation,[],[f11])).
% 2.46/1.00  
% 2.46/1.00  fof(f21,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.46/1.00    inference(flattening,[],[f20])).
% 2.46/1.00  
% 2.46/1.00  fof(f27,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.46/1.00    inference(nnf_transformation,[],[f21])).
% 2.46/1.00  
% 2.46/1.00  fof(f28,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.46/1.00    inference(flattening,[],[f27])).
% 2.46/1.00  
% 2.46/1.00  fof(f29,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.46/1.00    inference(rectify,[],[f28])).
% 2.46/1.00  
% 2.46/1.00  fof(f32,plain,(
% 2.46/1.00    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.46/1.00    introduced(choice_axiom,[])).
% 2.46/1.00  
% 2.46/1.00  fof(f31,plain,(
% 2.46/1.00    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.46/1.00    introduced(choice_axiom,[])).
% 2.46/1.00  
% 2.46/1.00  fof(f30,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.46/1.00    introduced(choice_axiom,[])).
% 2.46/1.00  
% 2.46/1.00  fof(f33,plain,(
% 2.46/1.00    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).
% 2.46/1.00  
% 2.46/1.00  fof(f48,plain,(
% 2.46/1.00    v2_pre_topc(sK0)),
% 2.46/1.00    inference(cnf_transformation,[],[f33])).
% 2.46/1.00  
% 2.46/1.00  fof(f49,plain,(
% 2.46/1.00    l1_pre_topc(sK0)),
% 2.46/1.00    inference(cnf_transformation,[],[f33])).
% 2.46/1.00  
% 2.46/1.00  fof(f51,plain,(
% 2.46/1.00    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f33])).
% 2.46/1.00  
% 2.46/1.00  fof(f50,plain,(
% 2.46/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.46/1.00    inference(cnf_transformation,[],[f33])).
% 2.46/1.00  
% 2.46/1.00  fof(f41,plain,(
% 2.46/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f25])).
% 2.46/1.00  
% 2.46/1.00  fof(f3,axiom,(
% 2.46/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f12,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.46/1.00    inference(ennf_transformation,[],[f3])).
% 2.46/1.00  
% 2.46/1.00  fof(f13,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.46/1.00    inference(flattening,[],[f12])).
% 2.46/1.00  
% 2.46/1.00  fof(f39,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f13])).
% 2.46/1.00  
% 2.46/1.00  fof(f9,axiom,(
% 2.46/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f19,plain,(
% 2.46/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.46/1.00    inference(ennf_transformation,[],[f9])).
% 2.46/1.00  
% 2.46/1.00  fof(f26,plain,(
% 2.46/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.46/1.00    inference(nnf_transformation,[],[f19])).
% 2.46/1.00  
% 2.46/1.00  fof(f47,plain,(
% 2.46/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f26])).
% 2.46/1.00  
% 2.46/1.00  fof(f8,axiom,(
% 2.46/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f17,plain,(
% 2.46/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.46/1.00    inference(ennf_transformation,[],[f8])).
% 2.46/1.00  
% 2.46/1.00  fof(f18,plain,(
% 2.46/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.46/1.00    inference(flattening,[],[f17])).
% 2.46/1.00  
% 2.46/1.00  fof(f45,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f18])).
% 2.46/1.00  
% 2.46/1.00  fof(f2,axiom,(
% 2.46/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f24,plain,(
% 2.46/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.46/1.00    inference(nnf_transformation,[],[f2])).
% 2.46/1.00  
% 2.46/1.00  fof(f37,plain,(
% 2.46/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.46/1.00    inference(cnf_transformation,[],[f24])).
% 2.46/1.00  
% 2.46/1.00  fof(f7,axiom,(
% 2.46/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f16,plain,(
% 2.46/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.46/1.00    inference(ennf_transformation,[],[f7])).
% 2.46/1.00  
% 2.46/1.00  fof(f44,plain,(
% 2.46/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f16])).
% 2.46/1.00  
% 2.46/1.00  fof(f1,axiom,(
% 2.46/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f22,plain,(
% 2.46/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.46/1.00    inference(nnf_transformation,[],[f1])).
% 2.46/1.00  
% 2.46/1.00  fof(f23,plain,(
% 2.46/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.46/1.00    inference(flattening,[],[f22])).
% 2.46/1.00  
% 2.46/1.00  fof(f36,plain,(
% 2.46/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f23])).
% 2.46/1.00  
% 2.46/1.00  fof(f35,plain,(
% 2.46/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.46/1.00    inference(cnf_transformation,[],[f23])).
% 2.46/1.00  
% 2.46/1.00  fof(f56,plain,(
% 2.46/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.46/1.00    inference(equality_resolution,[],[f35])).
% 2.46/1.00  
% 2.46/1.00  fof(f46,plain,(
% 2.46/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f26])).
% 2.46/1.00  
% 2.46/1.00  fof(f4,axiom,(
% 2.46/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f40,plain,(
% 2.46/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f4])).
% 2.46/1.00  
% 2.46/1.00  fof(f38,plain,(
% 2.46/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f24])).
% 2.46/1.00  
% 2.46/1.00  fof(f54,plain,(
% 2.46/1.00    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 2.46/1.00    inference(cnf_transformation,[],[f33])).
% 2.46/1.00  
% 2.46/1.00  fof(f52,plain,(
% 2.46/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 2.46/1.00    inference(cnf_transformation,[],[f33])).
% 2.46/1.00  
% 2.46/1.00  fof(f53,plain,(
% 2.46/1.00    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.46/1.00    inference(cnf_transformation,[],[f33])).
% 2.46/1.00  
% 2.46/1.00  fof(f55,plain,(
% 2.46/1.00    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 2.46/1.00    inference(cnf_transformation,[],[f33])).
% 2.46/1.00  
% 2.46/1.00  cnf(c_7,plain,
% 2.46/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1589,plain,
% 2.46/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.46/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_9,plain,
% 2.46/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.46/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.46/1.00      | ~ v2_pre_topc(X0)
% 2.46/1.00      | ~ l1_pre_topc(X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_21,negated_conjecture,
% 2.46/1.00      ( v2_pre_topc(sK0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_291,plain,
% 2.46/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.46/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.46/1.00      | ~ l1_pre_topc(X0)
% 2.46/1.00      | sK0 != X0 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_292,plain,
% 2.46/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ l1_pre_topc(sK0) ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_291]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_20,negated_conjecture,
% 2.46/1.00      ( l1_pre_topc(sK0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_296,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_292,c_20]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_297,plain,
% 2.46/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(renaming,[status(thm)],[c_296]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1581,plain,
% 2.46/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
% 2.46/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2843,plain,
% 2.46/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
% 2.46/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1589,c_1581]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_18,negated_conjecture,
% 2.46/1.00      ( v2_tops_1(sK1,sK0)
% 2.46/1.00      | ~ v3_pre_topc(X0,sK0)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ r1_tarski(X0,sK1)
% 2.46/1.00      | k1_xboole_0 = X0 ),
% 2.46/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1583,plain,
% 2.46/1.00      ( k1_xboole_0 = X0
% 2.46/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.46/1.00      | v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2846,plain,
% 2.46/1.00      ( k1_xboole_0 = X0
% 2.46/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.46/1.00      | v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1589,c_1583]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_19,negated_conjecture,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_24,plain,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_8,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1797,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1934,plain,
% 2.46/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1797]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1935,plain,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.46/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1813,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1)
% 2.46/1.00      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 2.46/1.00      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2205,plain,
% 2.46/1.00      ( r1_tarski(X0,u1_struct_0(sK0))
% 2.46/1.00      | ~ r1_tarski(X0,sK1)
% 2.46/1.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1813]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2206,plain,
% 2.46/1.00      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top
% 2.46/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_2205]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_4154,plain,
% 2.46/1.00      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.46/1.00      | k1_xboole_0 = X0
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_2846,c_24,c_1935,c_2206]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_4155,plain,
% 2.46/1.00      ( k1_xboole_0 = X0
% 2.46/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.46/1.00      | v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.46/1.00      inference(renaming,[status(thm)],[c_4154]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5096,plain,
% 2.46/1.00      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.46/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.46/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,X0),sK1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_2843,c_4155]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_12,plain,
% 2.46/1.00      ( v2_tops_1(X0,X1)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | ~ l1_pre_topc(X1)
% 2.46/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.46/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_327,plain,
% 2.46/1.00      ( v2_tops_1(X0,X1)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.46/1.00      | sK0 != X1 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_328,plain,
% 2.46/1.00      ( v2_tops_1(X0,sK0)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_327]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1731,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0)
% 2.46/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_328]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1732,plain,
% 2.46/1.00      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.46/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.46/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1731]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1582,plain,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2365,plain,
% 2.46/1.00      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1582,c_1581]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_11,plain,
% 2.46/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | ~ r1_tarski(X0,X2)
% 2.46/1.00      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.46/1.00      | ~ l1_pre_topc(X1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_342,plain,
% 2.46/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | ~ r1_tarski(X0,X2)
% 2.46/1.00      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.46/1.00      | sK0 != X1 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_343,plain,
% 2.46/1.00      ( ~ v3_pre_topc(X0,sK0)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ r1_tarski(X0,X1)
% 2.46/1.00      | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_342]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1578,plain,
% 2.46/1.00      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.46/1.00      | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2844,plain,
% 2.46/1.00      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.46/1.00      | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top
% 2.46/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1589,c_1578]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5586,plain,
% 2.46/1.00      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(X0,k1_tops_1(sK0,sK1)) = iProver_top
% 2.46/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1582,c_2844]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5891,plain,
% 2.46/1.00      ( r1_tarski(X0,k1_tops_1(sK0,sK1)) = iProver_top
% 2.46/1.00      | v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_5586,c_24,c_1935,c_2206]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5892,plain,
% 2.46/1.00      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(X0,k1_tops_1(sK0,sK1)) = iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.46/1.00      inference(renaming,[status(thm)],[c_5891]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1591,plain,
% 2.46/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.46/1.00      | r1_tarski(X1,X2) != iProver_top
% 2.46/1.00      | r1_tarski(X0,X2) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5900,plain,
% 2.46/1.00      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(X0,X1) = iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK1),X1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_5892,c_1591]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_4,plain,
% 2.46/1.00      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.46/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_57,plain,
% 2.46/1.00      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 2.46/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_10,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.46/1.00      | ~ l1_pre_topc(X1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_363,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.46/1.00      | sK0 != X1 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_364,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_363]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1734,plain,
% 2.46/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_364]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1735,plain,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1734]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_0,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.46/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1863,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 2.46/1.00      | ~ r1_tarski(k1_xboole_0,X0)
% 2.46/1.00      | k1_xboole_0 = X0 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2037,plain,
% 2.46/1.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.46/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1863]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1,plain,
% 2.46/1.00      ( r1_tarski(X0,X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2038,plain,
% 2.46/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2041,plain,
% 2.46/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_2038]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_13,plain,
% 2.46/1.00      ( ~ v2_tops_1(X0,X1)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | ~ l1_pre_topc(X1)
% 2.46/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.46/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_312,plain,
% 2.46/1.00      ( ~ v2_tops_1(X0,X1)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.46/1.00      | sK0 != X1 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_313,plain,
% 2.46/1.00      ( ~ v2_tops_1(X0,sK0)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_312]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1580,plain,
% 2.46/1.00      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.46/1.00      | v2_tops_1(X0,sK0) != iProver_top
% 2.46/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2551,plain,
% 2.46/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.46/1.00      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1582,c_1580]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1104,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.46/1.00      theory(equality) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1858,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1)
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
% 2.46/1.00      | k1_tops_1(sK0,sK1) != X0
% 2.46/1.00      | k1_xboole_0 != X1 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1104]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2120,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
% 2.46/1.00      | k1_tops_1(sK0,sK1) != X0
% 2.46/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1858]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2645,plain,
% 2.46/1.00      ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
% 2.46/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.46/1.00      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.46/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_2120]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2646,plain,
% 2.46/1.00      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.46/1.00      | k1_xboole_0 != k1_xboole_0
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) = iProver_top
% 2.46/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_2645]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_4164,plain,
% 2.46/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.46/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_2365,c_4155]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1978,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1)
% 2.46/1.00      | ~ r1_tarski(X1,k1_xboole_0)
% 2.46/1.00      | r1_tarski(X0,k1_xboole_0) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5807,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
% 2.46/1.00      | r1_tarski(X0,k1_xboole_0)
% 2.46/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1978]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5808,plain,
% 2.46/1.00      ( r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 2.46/1.00      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_5807]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6,plain,
% 2.46/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1590,plain,
% 2.46/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3073,plain,
% 2.46/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.46/1.00      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1590,c_1591]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1594,plain,
% 2.46/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.46/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1593,plain,
% 2.46/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.46/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2227,plain,
% 2.46/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1594,c_1593]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3099,plain,
% 2.46/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_2227,c_1590]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1595,plain,
% 2.46/1.00      ( X0 = X1
% 2.46/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.46/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3897,plain,
% 2.46/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_3099,c_1595]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5846,plain,
% 2.46/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.46/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_3073,c_3897]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6152,plain,
% 2.46/1.00      ( r1_tarski(X0,sK1) != iProver_top
% 2.46/1.00      | r1_tarski(X0,X1) = iProver_top
% 2.46/1.00      | v3_pre_topc(X0,sK0) != iProver_top ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_5900,c_24,c_57,c_1735,c_2037,c_2038,c_2041,c_2551,
% 2.46/1.00                 c_2646,c_4164,c_5808,c_5846,c_5892]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6153,plain,
% 2.46/1.00      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(X0,X1) = iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.46/1.00      inference(renaming,[status(thm)],[c_6152]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6160,plain,
% 2.46/1.00      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_2365,c_6153]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6781,plain,
% 2.46/1.00      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_6160,c_24,c_1735]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6792,plain,
% 2.46/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_6781,c_3897]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_7090,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_5096,c_24,c_1732,c_1735,c_2551,c_4164]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_15,negated_conjecture,
% 2.46/1.00      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1586,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | v3_pre_topc(sK2,sK0) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_7095,plain,
% 2.46/1.00      ( v3_pre_topc(sK2,sK0) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_7090,c_1586]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_7208,plain,
% 2.46/1.00      ( r1_tarski(sK2,X0) = iProver_top
% 2.46/1.00      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_7095,c_6153]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_17,negated_conjecture,
% 2.46/1.00      ( ~ v2_tops_1(sK1,sK0)
% 2.46/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1584,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2002,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | v3_pre_topc(sK2,sK0) != iProver_top
% 2.46/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,X0) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1584,c_1578]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_392,plain,
% 2.46/1.00      ( ~ v2_tops_1(sK1,sK0)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ r1_tarski(X0,X1)
% 2.46/1.00      | r1_tarski(X0,k1_tops_1(sK0,X1))
% 2.46/1.00      | sK0 != sK0
% 2.46/1.00      | sK2 != X0 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_343]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_393,plain,
% 2.46/1.00      ( ~ v2_tops_1(sK1,sK0)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ r1_tarski(sK2,X0)
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_392]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_397,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ v2_tops_1(sK1,sK0)
% 2.46/1.00      | ~ r1_tarski(sK2,X0)
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_393,c_17]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_398,plain,
% 2.46/1.00      ( ~ v2_tops_1(sK1,sK0)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ r1_tarski(sK2,X0)
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.46/1.00      inference(renaming,[status(thm)],[c_397]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_399,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,X0) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3612,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,X0) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_2002,c_399]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3622,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.46/1.00      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1582,c_3612]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_16,negated_conjecture,
% 2.46/1.00      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_29,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,sK1) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3792,plain,
% 2.46/1.00      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.46/1.00      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_3622,c_29]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3793,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 2.46/1.00      inference(renaming,[status(thm)],[c_3792]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3800,plain,
% 2.46/1.00      ( k4_xboole_0(sK2,k1_tops_1(sK0,sK1)) = k1_xboole_0
% 2.46/1.00      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_3793,c_1593]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3821,plain,
% 2.46/1.00      ( ~ v2_tops_1(sK1,sK0)
% 2.46/1.00      | k4_xboole_0(sK2,k1_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 2.46/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3800]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5084,plain,
% 2.46/1.00      ( k4_xboole_0(sK2,k1_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_3800,c_19,c_24,c_1731,c_1735,c_2551,c_3821,c_4164]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1592,plain,
% 2.46/1.00      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 2.46/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5088,plain,
% 2.46/1.00      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_5084,c_1592]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5619,plain,
% 2.46/1.00      ( r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_5088,c_1591]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_7720,plain,
% 2.46/1.00      ( r1_tarski(sK2,X0) = iProver_top ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_7208,c_24,c_1735,c_5619,c_6160]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_7731,plain,
% 2.46/1.00      ( sK2 = k1_xboole_0 ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_7720,c_3897]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1577,plain,
% 2.46/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1889,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1584,c_1577]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2901,plain,
% 2.46/1.00      ( k1_tops_1(sK0,sK2) = sK2
% 2.46/1.00      | v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1889,c_1595]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1897,plain,
% 2.46/1.00      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 2.46/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1889]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3621,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top
% 2.46/1.00      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1584,c_3612]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3765,plain,
% 2.46/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top ),
% 2.46/1.00      inference(forward_subsumption_resolution,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_3621,c_1594]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3768,plain,
% 2.46/1.00      ( k1_tops_1(sK0,sK2) = sK2
% 2.46/1.00      | v2_tops_1(sK1,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_3765,c_1595]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3789,plain,
% 2.46/1.00      ( ~ v2_tops_1(sK1,sK0)
% 2.46/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.46/1.00      | k1_tops_1(sK0,sK2) = sK2 ),
% 2.46/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3768]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5261,plain,
% 2.46/1.00      ( k1_tops_1(sK0,sK2) = sK2 ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_2901,c_19,c_24,c_1731,c_1735,c_1897,c_2551,c_3789,
% 2.46/1.00                 c_4164]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1579,plain,
% 2.46/1.00      ( k1_tops_1(sK0,X0) != k1_xboole_0
% 2.46/1.00      | v2_tops_1(X0,sK0) = iProver_top
% 2.46/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5284,plain,
% 2.46/1.00      ( sK2 != k1_xboole_0
% 2.46/1.00      | v2_tops_1(sK2,sK0) = iProver_top
% 2.46/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_5261,c_1579]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_14,negated_conjecture,
% 2.46/1.00      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 2.46/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_624,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.46/1.00      | sK0 != sK0
% 2.46/1.00      | sK1 != X0
% 2.46/1.00      | sK2 != k1_xboole_0 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_328]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_625,plain,
% 2.46/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.46/1.00      | sK2 != k1_xboole_0 ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_624]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_627,plain,
% 2.46/1.00      ( k1_tops_1(sK0,sK1) != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_625,c_19]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5399,plain,
% 2.46/1.00      ( sK2 != k1_xboole_0 ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_5284,c_19,c_24,c_625,c_1735,c_2551,c_4164]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(contradiction,plain,
% 2.46/1.00      ( $false ),
% 2.46/1.00      inference(minisat,[status(thm)],[c_7731,c_5399]) ).
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  ------                               Statistics
% 2.46/1.00  
% 2.46/1.00  ------ General
% 2.46/1.00  
% 2.46/1.00  abstr_ref_over_cycles:                  0
% 2.46/1.00  abstr_ref_under_cycles:                 0
% 2.46/1.00  gc_basic_clause_elim:                   0
% 2.46/1.00  forced_gc_time:                         0
% 2.46/1.00  parsing_time:                           0.01
% 2.46/1.00  unif_index_cands_time:                  0.
% 2.46/1.00  unif_index_add_time:                    0.
% 2.46/1.00  orderings_time:                         0.
% 2.46/1.00  out_proof_time:                         0.011
% 2.46/1.00  total_time:                             0.225
% 2.46/1.00  num_of_symbols:                         45
% 2.46/1.00  num_of_terms:                           5386
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing
% 2.46/1.00  
% 2.46/1.00  num_of_splits:                          0
% 2.46/1.00  num_of_split_atoms:                     0
% 2.46/1.00  num_of_reused_defs:                     0
% 2.46/1.00  num_eq_ax_congr_red:                    10
% 2.46/1.00  num_of_sem_filtered_clauses:            1
% 2.46/1.00  num_of_subtypes:                        0
% 2.46/1.00  monotx_restored_types:                  0
% 2.46/1.00  sat_num_of_epr_types:                   0
% 2.46/1.00  sat_num_of_non_cyclic_types:            0
% 2.46/1.00  sat_guarded_non_collapsed_types:        0
% 2.46/1.00  num_pure_diseq_elim:                    0
% 2.46/1.00  simp_replaced_by:                       0
% 2.46/1.00  res_preprocessed:                       97
% 2.46/1.00  prep_upred:                             0
% 2.46/1.00  prep_unflattend:                        23
% 2.46/1.00  smt_new_axioms:                         0
% 2.46/1.00  pred_elim_cands:                        4
% 2.46/1.00  pred_elim:                              2
% 2.46/1.00  pred_elim_cl:                           2
% 2.46/1.00  pred_elim_cycles:                       6
% 2.46/1.00  merged_defs:                            16
% 2.46/1.00  merged_defs_ncl:                        0
% 2.46/1.00  bin_hyper_res:                          16
% 2.46/1.00  prep_cycles:                            4
% 2.46/1.00  pred_elim_time:                         0.011
% 2.46/1.00  splitting_time:                         0.
% 2.46/1.00  sem_filter_time:                        0.
% 2.46/1.00  monotx_time:                            0.
% 2.46/1.00  subtype_inf_time:                       0.
% 2.46/1.00  
% 2.46/1.00  ------ Problem properties
% 2.46/1.00  
% 2.46/1.00  clauses:                                19
% 2.46/1.00  conjectures:                            6
% 2.46/1.00  epr:                                    6
% 2.46/1.00  horn:                                   18
% 2.46/1.00  ground:                                 5
% 2.46/1.00  unary:                                  3
% 2.46/1.00  binary:                                 10
% 2.46/1.00  lits:                                   45
% 2.46/1.00  lits_eq:                                7
% 2.46/1.00  fd_pure:                                0
% 2.46/1.00  fd_pseudo:                              0
% 2.46/1.00  fd_cond:                                1
% 2.46/1.00  fd_pseudo_cond:                         1
% 2.46/1.00  ac_symbols:                             0
% 2.46/1.00  
% 2.46/1.00  ------ Propositional Solver
% 2.46/1.00  
% 2.46/1.00  prop_solver_calls:                      28
% 2.46/1.00  prop_fast_solver_calls:                 937
% 2.46/1.00  smt_solver_calls:                       0
% 2.46/1.00  smt_fast_solver_calls:                  0
% 2.46/1.00  prop_num_of_clauses:                    2816
% 2.46/1.00  prop_preprocess_simplified:             6660
% 2.46/1.00  prop_fo_subsumed:                       51
% 2.46/1.00  prop_solver_time:                       0.
% 2.46/1.00  smt_solver_time:                        0.
% 2.46/1.00  smt_fast_solver_time:                   0.
% 2.46/1.00  prop_fast_solver_time:                  0.
% 2.46/1.00  prop_unsat_core_time:                   0.
% 2.46/1.00  
% 2.46/1.00  ------ QBF
% 2.46/1.00  
% 2.46/1.00  qbf_q_res:                              0
% 2.46/1.00  qbf_num_tautologies:                    0
% 2.46/1.00  qbf_prep_cycles:                        0
% 2.46/1.00  
% 2.46/1.00  ------ BMC1
% 2.46/1.00  
% 2.46/1.00  bmc1_current_bound:                     -1
% 2.46/1.00  bmc1_last_solved_bound:                 -1
% 2.46/1.00  bmc1_unsat_core_size:                   -1
% 2.46/1.00  bmc1_unsat_core_parents_size:           -1
% 2.46/1.00  bmc1_merge_next_fun:                    0
% 2.46/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.46/1.00  
% 2.46/1.00  ------ Instantiation
% 2.46/1.00  
% 2.46/1.00  inst_num_of_clauses:                    793
% 2.46/1.00  inst_num_in_passive:                    129
% 2.46/1.00  inst_num_in_active:                     403
% 2.46/1.00  inst_num_in_unprocessed:                262
% 2.46/1.00  inst_num_of_loops:                      430
% 2.46/1.00  inst_num_of_learning_restarts:          0
% 2.46/1.00  inst_num_moves_active_passive:          23
% 2.46/1.00  inst_lit_activity:                      0
% 2.46/1.00  inst_lit_activity_moves:                0
% 2.46/1.00  inst_num_tautologies:                   0
% 2.46/1.00  inst_num_prop_implied:                  0
% 2.46/1.00  inst_num_existing_simplified:           0
% 2.46/1.00  inst_num_eq_res_simplified:             0
% 2.46/1.00  inst_num_child_elim:                    0
% 2.46/1.00  inst_num_of_dismatching_blockings:      336
% 2.46/1.00  inst_num_of_non_proper_insts:           1178
% 2.46/1.00  inst_num_of_duplicates:                 0
% 2.46/1.00  inst_inst_num_from_inst_to_res:         0
% 2.46/1.00  inst_dismatching_checking_time:         0.
% 2.46/1.00  
% 2.46/1.00  ------ Resolution
% 2.46/1.00  
% 2.46/1.00  res_num_of_clauses:                     0
% 2.46/1.00  res_num_in_passive:                     0
% 2.46/1.00  res_num_in_active:                      0
% 2.46/1.00  res_num_of_loops:                       101
% 2.46/1.00  res_forward_subset_subsumed:            77
% 2.46/1.00  res_backward_subset_subsumed:           4
% 2.46/1.00  res_forward_subsumed:                   0
% 2.46/1.00  res_backward_subsumed:                  0
% 2.46/1.00  res_forward_subsumption_resolution:     0
% 2.46/1.00  res_backward_subsumption_resolution:    0
% 2.46/1.00  res_clause_to_clause_subsumption:       845
% 2.46/1.00  res_orphan_elimination:                 0
% 2.46/1.00  res_tautology_del:                      163
% 2.46/1.00  res_num_eq_res_simplified:              0
% 2.46/1.00  res_num_sel_changes:                    0
% 2.46/1.00  res_moves_from_active_to_pass:          0
% 2.46/1.00  
% 2.46/1.00  ------ Superposition
% 2.46/1.00  
% 2.46/1.00  sup_time_total:                         0.
% 2.46/1.00  sup_time_generating:                    0.
% 2.46/1.00  sup_time_sim_full:                      0.
% 2.46/1.00  sup_time_sim_immed:                     0.
% 2.46/1.00  
% 2.46/1.00  sup_num_of_clauses:                     107
% 2.46/1.00  sup_num_in_active:                      59
% 2.46/1.00  sup_num_in_passive:                     48
% 2.46/1.00  sup_num_of_loops:                       84
% 2.46/1.00  sup_fw_superposition:                   81
% 2.46/1.00  sup_bw_superposition:                   135
% 2.46/1.00  sup_immediate_simplified:               50
% 2.46/1.00  sup_given_eliminated:                   2
% 2.46/1.00  comparisons_done:                       0
% 2.46/1.00  comparisons_avoided:                    0
% 2.46/1.00  
% 2.46/1.00  ------ Simplifications
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  sim_fw_subset_subsumed:                 12
% 2.46/1.00  sim_bw_subset_subsumed:                 15
% 2.46/1.00  sim_fw_subsumed:                        24
% 2.46/1.00  sim_bw_subsumed:                        0
% 2.46/1.00  sim_fw_subsumption_res:                 3
% 2.46/1.00  sim_bw_subsumption_res:                 0
% 2.46/1.00  sim_tautology_del:                      7
% 2.46/1.00  sim_eq_tautology_del:                   8
% 2.46/1.00  sim_eq_res_simp:                        0
% 2.46/1.00  sim_fw_demodulated:                     5
% 2.46/1.00  sim_bw_demodulated:                     27
% 2.46/1.00  sim_light_normalised:                   12
% 2.46/1.00  sim_joinable_taut:                      0
% 2.46/1.00  sim_joinable_simp:                      0
% 2.46/1.00  sim_ac_normalised:                      0
% 2.46/1.00  sim_smt_subsumption:                    0
% 2.46/1.00  
%------------------------------------------------------------------------------
