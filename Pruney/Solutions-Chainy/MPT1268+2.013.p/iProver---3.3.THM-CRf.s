%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:04 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  160 (2892 expanded)
%              Number of clauses        :  106 ( 749 expanded)
%              Number of leaves         :   13 ( 691 expanded)
%              Depth                    :   25
%              Number of atoms          :  551 (24098 expanded)
%              Number of equality atoms :  204 (4296 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31,f30,f29])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f36,plain,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f38,f37])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1480,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_259,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_260,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_260,c_18])).

cnf(c_265,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_1479,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_2402,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1479])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1487,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1481,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2155,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1481])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1727,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1837,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_1838,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1837])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1738,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1984,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_1985,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1984])).

cnf(c_3632,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | v2_tops_1(sK1,sK0) = iProver_top
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2155,c_22,c_1838,c_1985])).

cnf(c_3633,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3632])).

cnf(c_3642,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2402,c_3633])).

cnf(c_10,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_295,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_296,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_1615,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_1616,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1615])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_1618,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_1619,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1618])).

cnf(c_6237,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3642,c_22,c_1616,c_1619])).

cnf(c_11,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_280,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_281,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_1478,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_2610,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1478])).

cnf(c_6242,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6237,c_2610])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1490,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1482,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_310,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_311,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_1476,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_1886,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_1476])).

cnf(c_26,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_360,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1))
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_311])).

cnf(c_361,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_362,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_3230,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1886,c_26,c_362])).

cnf(c_3241,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_3230])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3373,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3241,c_27])).

cnf(c_3374,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3373])).

cnf(c_1489,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3380,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3374,c_1489])).

cnf(c_5209,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3380,c_22,c_1616,c_1619,c_3642])).

cnf(c_5217,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1490,c_5209])).

cnf(c_6360,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6242,c_5217])).

cnf(c_1638,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4859,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_1475,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_1795,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_1475])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1491,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2733,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1491])).

cnf(c_3240,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_3230])).

cnf(c_3352,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3240,c_1490])).

cnf(c_3354,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3352,c_1491])).

cnf(c_4448,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2733,c_22,c_1616,c_1619,c_1795,c_3354,c_3642])).

cnf(c_4452,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4448,c_22,c_1616,c_1619,c_1795,c_3354,c_3642])).

cnf(c_2609,plain,
    ( k1_tops_1(sK0,sK2) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | v2_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_1478])).

cnf(c_4458,plain,
    ( sK2 = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | v2_tops_1(sK2,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4452,c_2609])).

cnf(c_12,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_296])).

cnf(c_593,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_595,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_17])).

cnf(c_4617,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v2_tops_1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4458,c_17,c_22,c_593,c_1616,c_1619,c_2610,c_3642])).

cnf(c_4621,plain,
    ( v2_tops_1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4617,c_17,c_22,c_593,c_1616,c_1619,c_2610,c_3642,c_4458])).

cnf(c_4623,plain,
    ( ~ v2_tops_1(sK2,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4621])).

cnf(c_4536,plain,
    ( v2_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_2645,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1489])).

cnf(c_4401,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2645,c_22,c_1616,c_1619,c_3642])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1488,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1486,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2024,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1486])).

cnf(c_2760,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2024,c_1491])).

cnf(c_4412,plain,
    ( k1_tops_1(sK0,sK2) = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4401,c_2760])).

cnf(c_2025,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_1486])).

cnf(c_2642,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2025,c_1489])).

cnf(c_4299,plain,
    ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2642,c_22,c_1616,c_1619,c_3642])).

cnf(c_4307,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1490,c_4299])).

cnf(c_4308,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4307])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6360,c_4859,c_4623,c_4536,c_4412,c_4308])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:08:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.44/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.02  
% 2.44/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/1.02  
% 2.44/1.02  ------  iProver source info
% 2.44/1.02  
% 2.44/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.44/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/1.02  git: non_committed_changes: false
% 2.44/1.02  git: last_make_outside_of_git: false
% 2.44/1.02  
% 2.44/1.02  ------ 
% 2.44/1.02  
% 2.44/1.02  ------ Input Options
% 2.44/1.02  
% 2.44/1.02  --out_options                           all
% 2.44/1.02  --tptp_safe_out                         true
% 2.44/1.02  --problem_path                          ""
% 2.44/1.02  --include_path                          ""
% 2.44/1.02  --clausifier                            res/vclausify_rel
% 2.44/1.02  --clausifier_options                    --mode clausify
% 2.44/1.02  --stdin                                 false
% 2.44/1.02  --stats_out                             all
% 2.44/1.02  
% 2.44/1.02  ------ General Options
% 2.44/1.02  
% 2.44/1.02  --fof                                   false
% 2.44/1.02  --time_out_real                         305.
% 2.44/1.02  --time_out_virtual                      -1.
% 2.44/1.02  --symbol_type_check                     false
% 2.44/1.02  --clausify_out                          false
% 2.44/1.02  --sig_cnt_out                           false
% 2.44/1.02  --trig_cnt_out                          false
% 2.44/1.02  --trig_cnt_out_tolerance                1.
% 2.44/1.02  --trig_cnt_out_sk_spl                   false
% 2.44/1.02  --abstr_cl_out                          false
% 2.44/1.02  
% 2.44/1.02  ------ Global Options
% 2.44/1.02  
% 2.44/1.02  --schedule                              default
% 2.44/1.02  --add_important_lit                     false
% 2.44/1.02  --prop_solver_per_cl                    1000
% 2.44/1.02  --min_unsat_core                        false
% 2.44/1.02  --soft_assumptions                      false
% 2.44/1.02  --soft_lemma_size                       3
% 2.44/1.02  --prop_impl_unit_size                   0
% 2.44/1.02  --prop_impl_unit                        []
% 2.44/1.02  --share_sel_clauses                     true
% 2.44/1.02  --reset_solvers                         false
% 2.44/1.02  --bc_imp_inh                            [conj_cone]
% 2.44/1.02  --conj_cone_tolerance                   3.
% 2.44/1.02  --extra_neg_conj                        none
% 2.44/1.02  --large_theory_mode                     true
% 2.44/1.02  --prolific_symb_bound                   200
% 2.44/1.02  --lt_threshold                          2000
% 2.44/1.02  --clause_weak_htbl                      true
% 2.44/1.02  --gc_record_bc_elim                     false
% 2.44/1.02  
% 2.44/1.02  ------ Preprocessing Options
% 2.44/1.02  
% 2.44/1.02  --preprocessing_flag                    true
% 2.44/1.02  --time_out_prep_mult                    0.1
% 2.44/1.02  --splitting_mode                        input
% 2.44/1.02  --splitting_grd                         true
% 2.44/1.02  --splitting_cvd                         false
% 2.44/1.02  --splitting_cvd_svl                     false
% 2.44/1.02  --splitting_nvd                         32
% 2.44/1.02  --sub_typing                            true
% 2.44/1.02  --prep_gs_sim                           true
% 2.44/1.02  --prep_unflatten                        true
% 2.44/1.02  --prep_res_sim                          true
% 2.44/1.02  --prep_upred                            true
% 2.44/1.02  --prep_sem_filter                       exhaustive
% 2.44/1.02  --prep_sem_filter_out                   false
% 2.44/1.02  --pred_elim                             true
% 2.44/1.02  --res_sim_input                         true
% 2.44/1.02  --eq_ax_congr_red                       true
% 2.44/1.02  --pure_diseq_elim                       true
% 2.44/1.02  --brand_transform                       false
% 2.44/1.02  --non_eq_to_eq                          false
% 2.44/1.02  --prep_def_merge                        true
% 2.44/1.02  --prep_def_merge_prop_impl              false
% 2.44/1.02  --prep_def_merge_mbd                    true
% 2.44/1.02  --prep_def_merge_tr_red                 false
% 2.44/1.02  --prep_def_merge_tr_cl                  false
% 2.44/1.02  --smt_preprocessing                     true
% 2.44/1.02  --smt_ac_axioms                         fast
% 2.44/1.02  --preprocessed_out                      false
% 2.44/1.02  --preprocessed_stats                    false
% 2.44/1.02  
% 2.44/1.02  ------ Abstraction refinement Options
% 2.44/1.02  
% 2.44/1.02  --abstr_ref                             []
% 2.44/1.02  --abstr_ref_prep                        false
% 2.44/1.02  --abstr_ref_until_sat                   false
% 2.44/1.02  --abstr_ref_sig_restrict                funpre
% 2.44/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.02  --abstr_ref_under                       []
% 2.44/1.02  
% 2.44/1.02  ------ SAT Options
% 2.44/1.02  
% 2.44/1.02  --sat_mode                              false
% 2.44/1.02  --sat_fm_restart_options                ""
% 2.44/1.02  --sat_gr_def                            false
% 2.44/1.02  --sat_epr_types                         true
% 2.44/1.02  --sat_non_cyclic_types                  false
% 2.44/1.02  --sat_finite_models                     false
% 2.44/1.02  --sat_fm_lemmas                         false
% 2.44/1.02  --sat_fm_prep                           false
% 2.44/1.02  --sat_fm_uc_incr                        true
% 2.44/1.02  --sat_out_model                         small
% 2.44/1.02  --sat_out_clauses                       false
% 2.44/1.02  
% 2.44/1.02  ------ QBF Options
% 2.44/1.02  
% 2.44/1.02  --qbf_mode                              false
% 2.44/1.02  --qbf_elim_univ                         false
% 2.44/1.02  --qbf_dom_inst                          none
% 2.44/1.02  --qbf_dom_pre_inst                      false
% 2.44/1.02  --qbf_sk_in                             false
% 2.44/1.02  --qbf_pred_elim                         true
% 2.44/1.02  --qbf_split                             512
% 2.44/1.02  
% 2.44/1.02  ------ BMC1 Options
% 2.44/1.02  
% 2.44/1.02  --bmc1_incremental                      false
% 2.44/1.02  --bmc1_axioms                           reachable_all
% 2.44/1.02  --bmc1_min_bound                        0
% 2.44/1.02  --bmc1_max_bound                        -1
% 2.44/1.02  --bmc1_max_bound_default                -1
% 2.44/1.02  --bmc1_symbol_reachability              true
% 2.44/1.02  --bmc1_property_lemmas                  false
% 2.44/1.02  --bmc1_k_induction                      false
% 2.44/1.02  --bmc1_non_equiv_states                 false
% 2.44/1.02  --bmc1_deadlock                         false
% 2.44/1.02  --bmc1_ucm                              false
% 2.44/1.02  --bmc1_add_unsat_core                   none
% 2.44/1.02  --bmc1_unsat_core_children              false
% 2.44/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.02  --bmc1_out_stat                         full
% 2.44/1.02  --bmc1_ground_init                      false
% 2.44/1.02  --bmc1_pre_inst_next_state              false
% 2.44/1.02  --bmc1_pre_inst_state                   false
% 2.44/1.02  --bmc1_pre_inst_reach_state             false
% 2.44/1.02  --bmc1_out_unsat_core                   false
% 2.44/1.02  --bmc1_aig_witness_out                  false
% 2.44/1.02  --bmc1_verbose                          false
% 2.44/1.02  --bmc1_dump_clauses_tptp                false
% 2.44/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.02  --bmc1_dump_file                        -
% 2.44/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.02  --bmc1_ucm_extend_mode                  1
% 2.44/1.02  --bmc1_ucm_init_mode                    2
% 2.44/1.02  --bmc1_ucm_cone_mode                    none
% 2.44/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.02  --bmc1_ucm_relax_model                  4
% 2.44/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.02  --bmc1_ucm_layered_model                none
% 2.44/1.02  --bmc1_ucm_max_lemma_size               10
% 2.44/1.02  
% 2.44/1.02  ------ AIG Options
% 2.44/1.02  
% 2.44/1.02  --aig_mode                              false
% 2.44/1.02  
% 2.44/1.02  ------ Instantiation Options
% 2.44/1.02  
% 2.44/1.02  --instantiation_flag                    true
% 2.44/1.02  --inst_sos_flag                         false
% 2.44/1.02  --inst_sos_phase                        true
% 2.44/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.02  --inst_lit_sel_side                     num_symb
% 2.44/1.02  --inst_solver_per_active                1400
% 2.44/1.02  --inst_solver_calls_frac                1.
% 2.44/1.02  --inst_passive_queue_type               priority_queues
% 2.44/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.02  --inst_passive_queues_freq              [25;2]
% 2.44/1.02  --inst_dismatching                      true
% 2.44/1.02  --inst_eager_unprocessed_to_passive     true
% 2.44/1.02  --inst_prop_sim_given                   true
% 2.44/1.02  --inst_prop_sim_new                     false
% 2.44/1.02  --inst_subs_new                         false
% 2.44/1.02  --inst_eq_res_simp                      false
% 2.44/1.02  --inst_subs_given                       false
% 2.44/1.02  --inst_orphan_elimination               true
% 2.44/1.02  --inst_learning_loop_flag               true
% 2.44/1.02  --inst_learning_start                   3000
% 2.44/1.02  --inst_learning_factor                  2
% 2.44/1.02  --inst_start_prop_sim_after_learn       3
% 2.44/1.02  --inst_sel_renew                        solver
% 2.44/1.02  --inst_lit_activity_flag                true
% 2.44/1.02  --inst_restr_to_given                   false
% 2.44/1.02  --inst_activity_threshold               500
% 2.44/1.02  --inst_out_proof                        true
% 2.44/1.02  
% 2.44/1.02  ------ Resolution Options
% 2.44/1.02  
% 2.44/1.02  --resolution_flag                       true
% 2.44/1.02  --res_lit_sel                           adaptive
% 2.44/1.02  --res_lit_sel_side                      none
% 2.44/1.02  --res_ordering                          kbo
% 2.44/1.02  --res_to_prop_solver                    active
% 2.44/1.02  --res_prop_simpl_new                    false
% 2.44/1.02  --res_prop_simpl_given                  true
% 2.44/1.02  --res_passive_queue_type                priority_queues
% 2.44/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.02  --res_passive_queues_freq               [15;5]
% 2.44/1.02  --res_forward_subs                      full
% 2.44/1.02  --res_backward_subs                     full
% 2.44/1.02  --res_forward_subs_resolution           true
% 2.44/1.02  --res_backward_subs_resolution          true
% 2.44/1.02  --res_orphan_elimination                true
% 2.44/1.02  --res_time_limit                        2.
% 2.44/1.02  --res_out_proof                         true
% 2.44/1.02  
% 2.44/1.02  ------ Superposition Options
% 2.44/1.02  
% 2.44/1.02  --superposition_flag                    true
% 2.44/1.02  --sup_passive_queue_type                priority_queues
% 2.44/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.02  --demod_completeness_check              fast
% 2.44/1.02  --demod_use_ground                      true
% 2.44/1.02  --sup_to_prop_solver                    passive
% 2.44/1.02  --sup_prop_simpl_new                    true
% 2.44/1.02  --sup_prop_simpl_given                  true
% 2.44/1.02  --sup_fun_splitting                     false
% 2.44/1.02  --sup_smt_interval                      50000
% 2.44/1.02  
% 2.44/1.02  ------ Superposition Simplification Setup
% 2.44/1.02  
% 2.44/1.02  --sup_indices_passive                   []
% 2.44/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.02  --sup_full_bw                           [BwDemod]
% 2.44/1.02  --sup_immed_triv                        [TrivRules]
% 2.44/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.02  --sup_immed_bw_main                     []
% 2.44/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.02  
% 2.44/1.02  ------ Combination Options
% 2.44/1.02  
% 2.44/1.02  --comb_res_mult                         3
% 2.44/1.02  --comb_sup_mult                         2
% 2.44/1.02  --comb_inst_mult                        10
% 2.44/1.02  
% 2.44/1.02  ------ Debug Options
% 2.44/1.02  
% 2.44/1.02  --dbg_backtrace                         false
% 2.44/1.02  --dbg_dump_prop_clauses                 false
% 2.44/1.02  --dbg_dump_prop_clauses_file            -
% 2.44/1.02  --dbg_out_stat                          false
% 2.44/1.02  ------ Parsing...
% 2.44/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/1.02  
% 2.44/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.44/1.02  
% 2.44/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/1.02  
% 2.44/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/1.02  ------ Proving...
% 2.44/1.02  ------ Problem Properties 
% 2.44/1.02  
% 2.44/1.02  
% 2.44/1.02  clauses                                 17
% 2.44/1.02  conjectures                             6
% 2.44/1.02  EPR                                     6
% 2.44/1.02  Horn                                    16
% 2.44/1.02  unary                                   3
% 2.44/1.02  binary                                  8
% 2.44/1.02  lits                                    41
% 2.44/1.02  lits eq                                 5
% 2.44/1.02  fd_pure                                 0
% 2.44/1.02  fd_pseudo                               0
% 2.44/1.02  fd_cond                                 1
% 2.44/1.02  fd_pseudo_cond                          1
% 2.44/1.02  AC symbols                              0
% 2.44/1.02  
% 2.44/1.02  ------ Schedule dynamic 5 is on 
% 2.44/1.02  
% 2.44/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/1.02  
% 2.44/1.02  
% 2.44/1.02  ------ 
% 2.44/1.02  Current options:
% 2.44/1.02  ------ 
% 2.44/1.02  
% 2.44/1.02  ------ Input Options
% 2.44/1.02  
% 2.44/1.02  --out_options                           all
% 2.44/1.02  --tptp_safe_out                         true
% 2.44/1.02  --problem_path                          ""
% 2.44/1.02  --include_path                          ""
% 2.44/1.02  --clausifier                            res/vclausify_rel
% 2.44/1.02  --clausifier_options                    --mode clausify
% 2.44/1.02  --stdin                                 false
% 2.44/1.02  --stats_out                             all
% 2.44/1.02  
% 2.44/1.02  ------ General Options
% 2.44/1.02  
% 2.44/1.02  --fof                                   false
% 2.44/1.02  --time_out_real                         305.
% 2.44/1.02  --time_out_virtual                      -1.
% 2.44/1.02  --symbol_type_check                     false
% 2.44/1.02  --clausify_out                          false
% 2.44/1.02  --sig_cnt_out                           false
% 2.44/1.02  --trig_cnt_out                          false
% 2.44/1.02  --trig_cnt_out_tolerance                1.
% 2.44/1.02  --trig_cnt_out_sk_spl                   false
% 2.44/1.02  --abstr_cl_out                          false
% 2.44/1.02  
% 2.44/1.02  ------ Global Options
% 2.44/1.02  
% 2.44/1.02  --schedule                              default
% 2.44/1.02  --add_important_lit                     false
% 2.44/1.02  --prop_solver_per_cl                    1000
% 2.44/1.02  --min_unsat_core                        false
% 2.44/1.02  --soft_assumptions                      false
% 2.44/1.02  --soft_lemma_size                       3
% 2.44/1.02  --prop_impl_unit_size                   0
% 2.44/1.02  --prop_impl_unit                        []
% 2.44/1.02  --share_sel_clauses                     true
% 2.44/1.02  --reset_solvers                         false
% 2.44/1.02  --bc_imp_inh                            [conj_cone]
% 2.44/1.02  --conj_cone_tolerance                   3.
% 2.44/1.02  --extra_neg_conj                        none
% 2.44/1.02  --large_theory_mode                     true
% 2.44/1.02  --prolific_symb_bound                   200
% 2.44/1.02  --lt_threshold                          2000
% 2.44/1.02  --clause_weak_htbl                      true
% 2.44/1.02  --gc_record_bc_elim                     false
% 2.44/1.02  
% 2.44/1.02  ------ Preprocessing Options
% 2.44/1.02  
% 2.44/1.02  --preprocessing_flag                    true
% 2.44/1.02  --time_out_prep_mult                    0.1
% 2.44/1.02  --splitting_mode                        input
% 2.44/1.02  --splitting_grd                         true
% 2.44/1.02  --splitting_cvd                         false
% 2.44/1.02  --splitting_cvd_svl                     false
% 2.44/1.02  --splitting_nvd                         32
% 2.44/1.02  --sub_typing                            true
% 2.44/1.02  --prep_gs_sim                           true
% 2.44/1.02  --prep_unflatten                        true
% 2.44/1.02  --prep_res_sim                          true
% 2.44/1.02  --prep_upred                            true
% 2.44/1.02  --prep_sem_filter                       exhaustive
% 2.44/1.02  --prep_sem_filter_out                   false
% 2.44/1.02  --pred_elim                             true
% 2.44/1.02  --res_sim_input                         true
% 2.44/1.02  --eq_ax_congr_red                       true
% 2.44/1.02  --pure_diseq_elim                       true
% 2.44/1.02  --brand_transform                       false
% 2.44/1.02  --non_eq_to_eq                          false
% 2.44/1.02  --prep_def_merge                        true
% 2.44/1.02  --prep_def_merge_prop_impl              false
% 2.44/1.02  --prep_def_merge_mbd                    true
% 2.44/1.02  --prep_def_merge_tr_red                 false
% 2.44/1.02  --prep_def_merge_tr_cl                  false
% 2.44/1.02  --smt_preprocessing                     true
% 2.44/1.02  --smt_ac_axioms                         fast
% 2.44/1.02  --preprocessed_out                      false
% 2.44/1.02  --preprocessed_stats                    false
% 2.44/1.02  
% 2.44/1.02  ------ Abstraction refinement Options
% 2.44/1.02  
% 2.44/1.02  --abstr_ref                             []
% 2.44/1.02  --abstr_ref_prep                        false
% 2.44/1.02  --abstr_ref_until_sat                   false
% 2.44/1.02  --abstr_ref_sig_restrict                funpre
% 2.44/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.02  --abstr_ref_under                       []
% 2.44/1.02  
% 2.44/1.02  ------ SAT Options
% 2.44/1.02  
% 2.44/1.02  --sat_mode                              false
% 2.44/1.02  --sat_fm_restart_options                ""
% 2.44/1.02  --sat_gr_def                            false
% 2.44/1.02  --sat_epr_types                         true
% 2.44/1.02  --sat_non_cyclic_types                  false
% 2.44/1.02  --sat_finite_models                     false
% 2.44/1.02  --sat_fm_lemmas                         false
% 2.44/1.02  --sat_fm_prep                           false
% 2.44/1.02  --sat_fm_uc_incr                        true
% 2.44/1.02  --sat_out_model                         small
% 2.44/1.02  --sat_out_clauses                       false
% 2.44/1.02  
% 2.44/1.02  ------ QBF Options
% 2.44/1.02  
% 2.44/1.02  --qbf_mode                              false
% 2.44/1.02  --qbf_elim_univ                         false
% 2.44/1.02  --qbf_dom_inst                          none
% 2.44/1.02  --qbf_dom_pre_inst                      false
% 2.44/1.02  --qbf_sk_in                             false
% 2.44/1.02  --qbf_pred_elim                         true
% 2.44/1.02  --qbf_split                             512
% 2.44/1.02  
% 2.44/1.02  ------ BMC1 Options
% 2.44/1.02  
% 2.44/1.02  --bmc1_incremental                      false
% 2.44/1.02  --bmc1_axioms                           reachable_all
% 2.44/1.02  --bmc1_min_bound                        0
% 2.44/1.02  --bmc1_max_bound                        -1
% 2.44/1.02  --bmc1_max_bound_default                -1
% 2.44/1.02  --bmc1_symbol_reachability              true
% 2.44/1.02  --bmc1_property_lemmas                  false
% 2.44/1.02  --bmc1_k_induction                      false
% 2.44/1.02  --bmc1_non_equiv_states                 false
% 2.44/1.02  --bmc1_deadlock                         false
% 2.44/1.02  --bmc1_ucm                              false
% 2.44/1.02  --bmc1_add_unsat_core                   none
% 2.44/1.02  --bmc1_unsat_core_children              false
% 2.44/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.02  --bmc1_out_stat                         full
% 2.44/1.02  --bmc1_ground_init                      false
% 2.44/1.02  --bmc1_pre_inst_next_state              false
% 2.44/1.02  --bmc1_pre_inst_state                   false
% 2.44/1.02  --bmc1_pre_inst_reach_state             false
% 2.44/1.02  --bmc1_out_unsat_core                   false
% 2.44/1.02  --bmc1_aig_witness_out                  false
% 2.44/1.02  --bmc1_verbose                          false
% 2.44/1.02  --bmc1_dump_clauses_tptp                false
% 2.44/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.02  --bmc1_dump_file                        -
% 2.44/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.02  --bmc1_ucm_extend_mode                  1
% 2.44/1.02  --bmc1_ucm_init_mode                    2
% 2.44/1.02  --bmc1_ucm_cone_mode                    none
% 2.44/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.02  --bmc1_ucm_relax_model                  4
% 2.44/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.02  --bmc1_ucm_layered_model                none
% 2.44/1.02  --bmc1_ucm_max_lemma_size               10
% 2.44/1.02  
% 2.44/1.02  ------ AIG Options
% 2.44/1.02  
% 2.44/1.02  --aig_mode                              false
% 2.44/1.02  
% 2.44/1.02  ------ Instantiation Options
% 2.44/1.02  
% 2.44/1.02  --instantiation_flag                    true
% 2.44/1.02  --inst_sos_flag                         false
% 2.44/1.02  --inst_sos_phase                        true
% 2.44/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.02  --inst_lit_sel_side                     none
% 2.44/1.02  --inst_solver_per_active                1400
% 2.44/1.02  --inst_solver_calls_frac                1.
% 2.44/1.02  --inst_passive_queue_type               priority_queues
% 2.44/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.02  --inst_passive_queues_freq              [25;2]
% 2.44/1.02  --inst_dismatching                      true
% 2.44/1.02  --inst_eager_unprocessed_to_passive     true
% 2.44/1.02  --inst_prop_sim_given                   true
% 2.44/1.02  --inst_prop_sim_new                     false
% 2.44/1.02  --inst_subs_new                         false
% 2.44/1.02  --inst_eq_res_simp                      false
% 2.44/1.02  --inst_subs_given                       false
% 2.44/1.02  --inst_orphan_elimination               true
% 2.44/1.02  --inst_learning_loop_flag               true
% 2.44/1.02  --inst_learning_start                   3000
% 2.44/1.02  --inst_learning_factor                  2
% 2.44/1.02  --inst_start_prop_sim_after_learn       3
% 2.44/1.02  --inst_sel_renew                        solver
% 2.44/1.02  --inst_lit_activity_flag                true
% 2.44/1.02  --inst_restr_to_given                   false
% 2.44/1.02  --inst_activity_threshold               500
% 2.44/1.02  --inst_out_proof                        true
% 2.44/1.02  
% 2.44/1.02  ------ Resolution Options
% 2.44/1.02  
% 2.44/1.02  --resolution_flag                       false
% 2.44/1.02  --res_lit_sel                           adaptive
% 2.44/1.02  --res_lit_sel_side                      none
% 2.44/1.02  --res_ordering                          kbo
% 2.44/1.02  --res_to_prop_solver                    active
% 2.44/1.02  --res_prop_simpl_new                    false
% 2.44/1.02  --res_prop_simpl_given                  true
% 2.44/1.02  --res_passive_queue_type                priority_queues
% 2.44/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.02  --res_passive_queues_freq               [15;5]
% 2.44/1.02  --res_forward_subs                      full
% 2.44/1.02  --res_backward_subs                     full
% 2.44/1.02  --res_forward_subs_resolution           true
% 2.44/1.02  --res_backward_subs_resolution          true
% 2.44/1.02  --res_orphan_elimination                true
% 2.44/1.02  --res_time_limit                        2.
% 2.44/1.02  --res_out_proof                         true
% 2.44/1.02  
% 2.44/1.02  ------ Superposition Options
% 2.44/1.02  
% 2.44/1.02  --superposition_flag                    true
% 2.44/1.02  --sup_passive_queue_type                priority_queues
% 2.44/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.02  --demod_completeness_check              fast
% 2.44/1.02  --demod_use_ground                      true
% 2.44/1.02  --sup_to_prop_solver                    passive
% 2.44/1.02  --sup_prop_simpl_new                    true
% 2.44/1.02  --sup_prop_simpl_given                  true
% 2.44/1.02  --sup_fun_splitting                     false
% 2.44/1.02  --sup_smt_interval                      50000
% 2.44/1.02  
% 2.44/1.02  ------ Superposition Simplification Setup
% 2.44/1.02  
% 2.44/1.02  --sup_indices_passive                   []
% 2.44/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.02  --sup_full_bw                           [BwDemod]
% 2.44/1.02  --sup_immed_triv                        [TrivRules]
% 2.44/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.02  --sup_immed_bw_main                     []
% 2.44/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.02  
% 2.44/1.02  ------ Combination Options
% 2.44/1.02  
% 2.44/1.02  --comb_res_mult                         3
% 2.44/1.02  --comb_sup_mult                         2
% 2.44/1.02  --comb_inst_mult                        10
% 2.44/1.02  
% 2.44/1.02  ------ Debug Options
% 2.44/1.02  
% 2.44/1.02  --dbg_backtrace                         false
% 2.44/1.02  --dbg_dump_prop_clauses                 false
% 2.44/1.02  --dbg_dump_prop_clauses_file            -
% 2.44/1.02  --dbg_out_stat                          false
% 2.44/1.02  
% 2.44/1.02  
% 2.44/1.02  
% 2.44/1.02  
% 2.44/1.02  ------ Proving...
% 2.44/1.02  
% 2.44/1.02  
% 2.44/1.02  % SZS status Theorem for theBenchmark.p
% 2.44/1.02  
% 2.44/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/1.02  
% 2.44/1.02  fof(f10,conjecture,(
% 2.44/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.02  
% 2.44/1.02  fof(f11,negated_conjecture,(
% 2.44/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.44/1.02    inference(negated_conjecture,[],[f10])).
% 2.44/1.02  
% 2.44/1.02  fof(f20,plain,(
% 2.44/1.02    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.44/1.02    inference(ennf_transformation,[],[f11])).
% 2.44/1.02  
% 2.44/1.02  fof(f21,plain,(
% 2.44/1.02    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.44/1.02    inference(flattening,[],[f20])).
% 2.44/1.02  
% 2.44/1.02  fof(f26,plain,(
% 2.44/1.02    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.44/1.02    inference(nnf_transformation,[],[f21])).
% 2.44/1.02  
% 2.44/1.02  fof(f27,plain,(
% 2.44/1.02    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.44/1.02    inference(flattening,[],[f26])).
% 2.44/1.02  
% 2.44/1.02  fof(f28,plain,(
% 2.44/1.02    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.44/1.02    inference(rectify,[],[f27])).
% 2.44/1.02  
% 2.44/1.02  fof(f31,plain,(
% 2.44/1.02    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.44/1.02    introduced(choice_axiom,[])).
% 2.44/1.02  
% 2.44/1.02  fof(f30,plain,(
% 2.44/1.02    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.44/1.02    introduced(choice_axiom,[])).
% 2.44/1.02  
% 2.44/1.02  fof(f29,plain,(
% 2.44/1.02    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.44/1.02    introduced(choice_axiom,[])).
% 2.44/1.02  
% 2.44/1.02  fof(f32,plain,(
% 2.44/1.02    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.44/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31,f30,f29])).
% 2.44/1.02  
% 2.44/1.02  fof(f48,plain,(
% 2.44/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.44/1.02    inference(cnf_transformation,[],[f32])).
% 2.44/1.02  
% 2.44/1.02  fof(f6,axiom,(
% 2.44/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.02  
% 2.44/1.02  fof(f14,plain,(
% 2.44/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.44/1.02    inference(ennf_transformation,[],[f6])).
% 2.44/1.02  
% 2.44/1.02  fof(f15,plain,(
% 2.44/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.44/1.02    inference(flattening,[],[f14])).
% 2.44/1.02  
% 2.44/1.02  fof(f41,plain,(
% 2.44/1.02    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.44/1.02    inference(cnf_transformation,[],[f15])).
% 2.44/1.02  
% 2.44/1.02  fof(f46,plain,(
% 2.44/1.02    v2_pre_topc(sK0)),
% 2.44/1.02    inference(cnf_transformation,[],[f32])).
% 2.44/1.02  
% 2.44/1.02  fof(f47,plain,(
% 2.44/1.02    l1_pre_topc(sK0)),
% 2.44/1.02    inference(cnf_transformation,[],[f32])).
% 2.44/1.02  
% 2.44/1.02  fof(f5,axiom,(
% 2.44/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.02  
% 2.44/1.02  fof(f24,plain,(
% 2.44/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.44/1.02    inference(nnf_transformation,[],[f5])).
% 2.44/1.02  
% 2.44/1.02  fof(f40,plain,(
% 2.44/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.44/1.02    inference(cnf_transformation,[],[f24])).
% 2.44/1.02  
% 2.44/1.02  fof(f49,plain,(
% 2.44/1.02    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 2.44/1.02    inference(cnf_transformation,[],[f32])).
% 2.44/1.02  
% 2.44/1.02  fof(f39,plain,(
% 2.44/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.44/1.02    inference(cnf_transformation,[],[f24])).
% 2.44/1.02  
% 2.44/1.02  fof(f2,axiom,(
% 2.44/1.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.02  
% 2.44/1.02  fof(f12,plain,(
% 2.44/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.44/1.02    inference(ennf_transformation,[],[f2])).
% 2.44/1.02  
% 2.44/1.02  fof(f13,plain,(
% 2.44/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.44/1.02    inference(flattening,[],[f12])).
% 2.44/1.02  
% 2.44/1.02  fof(f36,plain,(
% 2.44/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.44/1.02    inference(cnf_transformation,[],[f13])).
% 2.44/1.02  
% 2.44/1.02  fof(f9,axiom,(
% 2.44/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.02  
% 2.44/1.02  fof(f19,plain,(
% 2.44/1.02    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.44/1.02    inference(ennf_transformation,[],[f9])).
% 2.44/1.02  
% 2.44/1.02  fof(f25,plain,(
% 2.44/1.02    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.44/1.02    inference(nnf_transformation,[],[f19])).
% 2.44/1.02  
% 2.44/1.02  fof(f45,plain,(
% 2.44/1.02    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.44/1.02    inference(cnf_transformation,[],[f25])).
% 2.44/1.02  
% 2.44/1.02  fof(f7,axiom,(
% 2.44/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.02  
% 2.44/1.02  fof(f16,plain,(
% 2.44/1.02    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.44/1.02    inference(ennf_transformation,[],[f7])).
% 2.44/1.02  
% 2.44/1.02  fof(f42,plain,(
% 2.44/1.02    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.44/1.02    inference(cnf_transformation,[],[f16])).
% 2.44/1.02  
% 2.44/1.02  fof(f44,plain,(
% 2.44/1.02    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.44/1.02    inference(cnf_transformation,[],[f25])).
% 2.44/1.02  
% 2.44/1.02  fof(f1,axiom,(
% 2.44/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.02  
% 2.44/1.02  fof(f22,plain,(
% 2.44/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.44/1.02    inference(nnf_transformation,[],[f1])).
% 2.44/1.02  
% 2.44/1.02  fof(f23,plain,(
% 2.44/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.44/1.02    inference(flattening,[],[f22])).
% 2.44/1.02  
% 2.44/1.02  fof(f34,plain,(
% 2.44/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.44/1.02    inference(cnf_transformation,[],[f23])).
% 2.44/1.02  
% 2.44/1.02  fof(f55,plain,(
% 2.44/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.44/1.02    inference(equality_resolution,[],[f34])).
% 2.44/1.02  
% 2.44/1.02  fof(f50,plain,(
% 2.44/1.02    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 2.44/1.02    inference(cnf_transformation,[],[f32])).
% 2.44/1.02  
% 2.44/1.02  fof(f8,axiom,(
% 2.44/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.02  
% 2.44/1.02  fof(f17,plain,(
% 2.44/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.44/1.02    inference(ennf_transformation,[],[f8])).
% 2.44/1.02  
% 2.44/1.02  fof(f18,plain,(
% 2.44/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.44/1.02    inference(flattening,[],[f17])).
% 2.44/1.02  
% 2.44/1.02  fof(f43,plain,(
% 2.44/1.02    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.44/1.02    inference(cnf_transformation,[],[f18])).
% 2.44/1.02  
% 2.44/1.02  fof(f52,plain,(
% 2.44/1.02    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 2.44/1.02    inference(cnf_transformation,[],[f32])).
% 2.44/1.02  
% 2.44/1.02  fof(f51,plain,(
% 2.44/1.02    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.44/1.02    inference(cnf_transformation,[],[f32])).
% 2.44/1.02  
% 2.44/1.02  fof(f35,plain,(
% 2.44/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.44/1.02    inference(cnf_transformation,[],[f23])).
% 2.44/1.02  
% 2.44/1.02  fof(f53,plain,(
% 2.44/1.02    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 2.44/1.02    inference(cnf_transformation,[],[f32])).
% 2.44/1.02  
% 2.44/1.02  fof(f4,axiom,(
% 2.44/1.02    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 2.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.02  
% 2.44/1.02  fof(f38,plain,(
% 2.44/1.02    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.44/1.02    inference(cnf_transformation,[],[f4])).
% 2.44/1.02  
% 2.44/1.02  fof(f3,axiom,(
% 2.44/1.02    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 2.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.02  
% 2.44/1.02  fof(f37,plain,(
% 2.44/1.02    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 2.44/1.02    inference(cnf_transformation,[],[f3])).
% 2.44/1.02  
% 2.44/1.02  fof(f54,plain,(
% 2.44/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.44/1.02    inference(definition_unfolding,[],[f38,f37])).
% 2.44/1.02  
% 2.44/1.02  cnf(c_17,negated_conjecture,
% 2.44/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.44/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1480,plain,
% 2.44/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_7,plain,
% 2.44/1.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.44/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.02      | ~ v2_pre_topc(X0)
% 2.44/1.02      | ~ l1_pre_topc(X0) ),
% 2.44/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_19,negated_conjecture,
% 2.44/1.02      ( v2_pre_topc(sK0) ),
% 2.44/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_259,plain,
% 2.44/1.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.44/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.02      | ~ l1_pre_topc(X0)
% 2.44/1.02      | sK0 != X0 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_260,plain,
% 2.44/1.02      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | ~ l1_pre_topc(sK0) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_259]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_18,negated_conjecture,
% 2.44/1.02      ( l1_pre_topc(sK0) ),
% 2.44/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_264,plain,
% 2.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_260,c_18]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_265,plain,
% 2.44/1.02      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.44/1.02      inference(renaming,[status(thm)],[c_264]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1479,plain,
% 2.44/1.02      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
% 2.44/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2402,plain,
% 2.44/1.02      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1480,c_1479]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_5,plain,
% 2.44/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.44/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1487,plain,
% 2.44/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.44/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_16,negated_conjecture,
% 2.44/1.02      ( v2_tops_1(sK1,sK0)
% 2.44/1.02      | ~ v3_pre_topc(X0,sK0)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | ~ r1_tarski(X0,sK1)
% 2.44/1.02      | k1_xboole_0 = X0 ),
% 2.44/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1481,plain,
% 2.44/1.02      ( k1_xboole_0 = X0
% 2.44/1.02      | v2_tops_1(sK1,sK0) = iProver_top
% 2.44/1.02      | v3_pre_topc(X0,sK0) != iProver_top
% 2.44/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.44/1.02      | r1_tarski(X0,sK1) != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2155,plain,
% 2.44/1.02      ( k1_xboole_0 = X0
% 2.44/1.02      | v2_tops_1(sK1,sK0) = iProver_top
% 2.44/1.02      | v3_pre_topc(X0,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.44/1.02      | r1_tarski(X0,sK1) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1487,c_1481]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_22,plain,
% 2.44/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_6,plain,
% 2.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.44/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1727,plain,
% 2.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1837,plain,
% 2.44/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_1727]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1838,plain,
% 2.44/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.44/1.02      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1837]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3,plain,
% 2.44/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.44/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1738,plain,
% 2.44/1.02      ( ~ r1_tarski(X0,X1)
% 2.44/1.02      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 2.44/1.02      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1984,plain,
% 2.44/1.02      ( r1_tarski(X0,u1_struct_0(sK0))
% 2.44/1.02      | ~ r1_tarski(X0,sK1)
% 2.44/1.02      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_1738]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1985,plain,
% 2.44/1.02      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 2.44/1.02      | r1_tarski(X0,sK1) != iProver_top
% 2.44/1.02      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1984]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3632,plain,
% 2.44/1.02      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.44/1.02      | v2_tops_1(sK1,sK0) = iProver_top
% 2.44/1.02      | k1_xboole_0 = X0
% 2.44/1.02      | r1_tarski(X0,sK1) != iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_2155,c_22,c_1838,c_1985]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3633,plain,
% 2.44/1.02      ( k1_xboole_0 = X0
% 2.44/1.02      | v2_tops_1(sK1,sK0) = iProver_top
% 2.44/1.02      | v3_pre_topc(X0,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(X0,sK1) != iProver_top ),
% 2.44/1.02      inference(renaming,[status(thm)],[c_3632]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3642,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.44/1.02      | v2_tops_1(sK1,sK0) = iProver_top
% 2.44/1.02      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_2402,c_3633]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_10,plain,
% 2.44/1.02      ( v2_tops_1(X0,X1)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.02      | ~ l1_pre_topc(X1)
% 2.44/1.02      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.44/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_295,plain,
% 2.44/1.02      ( v2_tops_1(X0,X1)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.02      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.44/1.02      | sK0 != X1 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_296,plain,
% 2.44/1.02      ( v2_tops_1(X0,sK0)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_295]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1615,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0)
% 2.44/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_296]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1616,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.44/1.02      | v2_tops_1(sK1,sK0) = iProver_top
% 2.44/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1615]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_8,plain,
% 2.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.44/1.02      | ~ l1_pre_topc(X1) ),
% 2.44/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_331,plain,
% 2.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.44/1.02      | sK0 != X1 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_332,plain,
% 2.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_331]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1618,plain,
% 2.44/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_332]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1619,plain,
% 2.44/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.44/1.02      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1618]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_6237,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_3642,c_22,c_1616,c_1619]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_11,plain,
% 2.44/1.02      ( ~ v2_tops_1(X0,X1)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.02      | ~ l1_pre_topc(X1)
% 2.44/1.02      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.44/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_280,plain,
% 2.44/1.02      ( ~ v2_tops_1(X0,X1)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.02      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.44/1.02      | sK0 != X1 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_281,plain,
% 2.44/1.02      ( ~ v2_tops_1(X0,sK0)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_280]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1478,plain,
% 2.44/1.02      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.44/1.02      | v2_tops_1(X0,sK0) != iProver_top
% 2.44/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2610,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.44/1.02      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1480,c_1478]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_6242,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_6237,c_2610]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1,plain,
% 2.44/1.02      ( r1_tarski(X0,X0) ),
% 2.44/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1490,plain,
% 2.44/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_15,negated_conjecture,
% 2.44/1.02      ( ~ v2_tops_1(sK1,sK0)
% 2.44/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.44/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1482,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_9,plain,
% 2.44/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.02      | ~ r1_tarski(X0,X2)
% 2.44/1.02      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.44/1.02      | ~ l1_pre_topc(X1) ),
% 2.44/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_310,plain,
% 2.44/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.02      | ~ r1_tarski(X0,X2)
% 2.44/1.02      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.44/1.02      | sK0 != X1 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_311,plain,
% 2.44/1.02      ( ~ v3_pre_topc(X0,sK0)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | ~ r1_tarski(X0,X1)
% 2.44/1.02      | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_310]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1476,plain,
% 2.44/1.02      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.44/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.44/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.44/1.02      | r1_tarski(X0,X1) != iProver_top
% 2.44/1.02      | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1886,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | v3_pre_topc(sK2,sK0) != iProver_top
% 2.44/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,X0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1482,c_1476]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_26,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_13,negated_conjecture,
% 2.44/1.02      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 2.44/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_360,plain,
% 2.44/1.02      ( ~ v2_tops_1(sK1,sK0)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | ~ r1_tarski(X0,X1)
% 2.44/1.02      | r1_tarski(X0,k1_tops_1(sK0,X1))
% 2.44/1.02      | sK0 != sK0
% 2.44/1.02      | sK2 != X0 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_311]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_361,plain,
% 2.44/1.02      ( ~ v2_tops_1(sK1,sK0)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | ~ r1_tarski(sK2,X0)
% 2.44/1.02      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_360]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_362,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.44/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,X0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3230,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,X0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_1886,c_26,c_362]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3241,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.44/1.02      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1480,c_3230]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_14,negated_conjecture,
% 2.44/1.02      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 2.44/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_27,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,sK1) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3373,plain,
% 2.44/1.02      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.44/1.02      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_3241,c_27]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3374,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 2.44/1.02      inference(renaming,[status(thm)],[c_3373]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1489,plain,
% 2.44/1.02      ( r1_tarski(X0,X1) != iProver_top
% 2.44/1.02      | r1_tarski(X1,X2) != iProver_top
% 2.44/1.02      | r1_tarski(X0,X2) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3380,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,X0) = iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_3374,c_1489]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_5209,plain,
% 2.44/1.02      ( r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,X0) = iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_3380,c_22,c_1616,c_1619,c_3642]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_5217,plain,
% 2.44/1.02      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1490,c_5209]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_6360,plain,
% 2.44/1.02      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.44/1.02      inference(demodulation,[status(thm)],[c_6242,c_5217]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1638,plain,
% 2.44/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4859,plain,
% 2.44/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_1638]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1475,plain,
% 2.44/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.44/1.02      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1795,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1482,c_1475]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_0,plain,
% 2.44/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.44/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1491,plain,
% 2.44/1.02      ( X0 = X1
% 2.44/1.02      | r1_tarski(X0,X1) != iProver_top
% 2.44/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2733,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK2) = sK2
% 2.44/1.02      | v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1795,c_1491]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3240,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top
% 2.44/1.02      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1482,c_3230]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3352,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top ),
% 2.44/1.02      inference(forward_subsumption_resolution,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_3240,c_1490]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3354,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK2) = sK2
% 2.44/1.02      | v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_3352,c_1491]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4448,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK2) = sK2
% 2.44/1.02      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_2733,c_22,c_1616,c_1619,c_1795,c_3354,c_3642]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4452,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK2) = sK2 ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_4448,c_22,c_1616,c_1619,c_1795,c_3354,c_3642]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2609,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK2) = k1_xboole_0
% 2.44/1.02      | v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | v2_tops_1(sK2,sK0) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1482,c_1478]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4458,plain,
% 2.44/1.02      ( sK2 = k1_xboole_0
% 2.44/1.02      | v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | v2_tops_1(sK2,sK0) != iProver_top ),
% 2.44/1.02      inference(demodulation,[status(thm)],[c_4452,c_2609]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_12,negated_conjecture,
% 2.44/1.02      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 2.44/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_592,plain,
% 2.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.44/1.02      | sK0 != sK0
% 2.44/1.02      | sK1 != X0
% 2.44/1.02      | sK2 != k1_xboole_0 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_296]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_593,plain,
% 2.44/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.44/1.02      | sK2 != k1_xboole_0 ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_592]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_595,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK1) != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_593,c_17]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4617,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | v2_tops_1(sK2,sK0) != iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_4458,c_17,c_22,c_593,c_1616,c_1619,c_2610,c_3642]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4621,plain,
% 2.44/1.02      ( v2_tops_1(sK2,sK0) != iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_4617,c_17,c_22,c_593,c_1616,c_1619,c_2610,c_3642,
% 2.44/1.02                 c_4458]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4623,plain,
% 2.44/1.02      ( ~ v2_tops_1(sK2,sK0) ),
% 2.44/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4621]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4536,plain,
% 2.44/1.02      ( v2_tops_1(sK2,sK0)
% 2.44/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.44/1.02      | k1_tops_1(sK0,sK2) != k1_xboole_0 ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_296]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2645,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
% 2.44/1.02      | r1_tarski(sK2,X0) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1795,c_1489]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4401,plain,
% 2.44/1.02      ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
% 2.44/1.02      | r1_tarski(sK2,X0) != iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_2645,c_22,c_1616,c_1619,c_3642]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4,plain,
% 2.44/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.44/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1488,plain,
% 2.44/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1486,plain,
% 2.44/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.44/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2024,plain,
% 2.44/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1488,c_1486]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2760,plain,
% 2.44/1.02      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_2024,c_1491]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4412,plain,
% 2.44/1.02      ( k1_tops_1(sK0,sK2) = k1_xboole_0
% 2.44/1.02      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_4401,c_2760]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2025,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1482,c_1486]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2642,plain,
% 2.44/1.02      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.44/1.02      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,X0) = iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_2025,c_1489]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4299,plain,
% 2.44/1.02      ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 2.44/1.02      | r1_tarski(sK2,X0) = iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_2642,c_22,c_1616,c_1619,c_3642]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4307,plain,
% 2.44/1.02      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1490,c_4299]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4308,plain,
% 2.44/1.02      ( r1_tarski(sK2,u1_struct_0(sK0)) ),
% 2.44/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4307]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(contradiction,plain,
% 2.44/1.02      ( $false ),
% 2.44/1.02      inference(minisat,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_6360,c_4859,c_4623,c_4536,c_4412,c_4308]) ).
% 2.44/1.02  
% 2.44/1.02  
% 2.44/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.02  
% 2.44/1.02  ------                               Statistics
% 2.44/1.02  
% 2.44/1.02  ------ General
% 2.44/1.02  
% 2.44/1.02  abstr_ref_over_cycles:                  0
% 2.44/1.02  abstr_ref_under_cycles:                 0
% 2.44/1.02  gc_basic_clause_elim:                   0
% 2.44/1.02  forced_gc_time:                         0
% 2.44/1.02  parsing_time:                           0.014
% 2.44/1.02  unif_index_cands_time:                  0.
% 2.44/1.02  unif_index_add_time:                    0.
% 2.44/1.02  orderings_time:                         0.
% 2.44/1.02  out_proof_time:                         0.012
% 2.44/1.02  total_time:                             0.229
% 2.44/1.02  num_of_symbols:                         44
% 2.44/1.02  num_of_terms:                           2966
% 2.44/1.02  
% 2.44/1.02  ------ Preprocessing
% 2.44/1.02  
% 2.44/1.02  num_of_splits:                          0
% 2.44/1.02  num_of_split_atoms:                     0
% 2.44/1.02  num_of_reused_defs:                     0
% 2.44/1.02  num_eq_ax_congr_red:                    4
% 2.44/1.02  num_of_sem_filtered_clauses:            1
% 2.44/1.02  num_of_subtypes:                        0
% 2.44/1.02  monotx_restored_types:                  0
% 2.44/1.02  sat_num_of_epr_types:                   0
% 2.44/1.02  sat_num_of_non_cyclic_types:            0
% 2.44/1.02  sat_guarded_non_collapsed_types:        0
% 2.44/1.02  num_pure_diseq_elim:                    0
% 2.44/1.02  simp_replaced_by:                       0
% 2.44/1.02  res_preprocessed:                       89
% 2.44/1.02  prep_upred:                             0
% 2.44/1.02  prep_unflattend:                        23
% 2.44/1.02  smt_new_axioms:                         0
% 2.44/1.02  pred_elim_cands:                        4
% 2.44/1.02  pred_elim:                              2
% 2.44/1.02  pred_elim_cl:                           2
% 2.44/1.02  pred_elim_cycles:                       6
% 2.44/1.02  merged_defs:                            8
% 2.44/1.02  merged_defs_ncl:                        0
% 2.44/1.02  bin_hyper_res:                          8
% 2.44/1.02  prep_cycles:                            4
% 2.44/1.02  pred_elim_time:                         0.013
% 2.44/1.02  splitting_time:                         0.
% 2.44/1.02  sem_filter_time:                        0.
% 2.44/1.02  monotx_time:                            0.001
% 2.44/1.02  subtype_inf_time:                       0.
% 2.44/1.02  
% 2.44/1.02  ------ Problem properties
% 2.44/1.02  
% 2.44/1.02  clauses:                                17
% 2.44/1.02  conjectures:                            6
% 2.44/1.02  epr:                                    6
% 2.44/1.02  horn:                                   16
% 2.44/1.02  ground:                                 5
% 2.44/1.02  unary:                                  3
% 2.44/1.02  binary:                                 8
% 2.44/1.02  lits:                                   41
% 2.44/1.02  lits_eq:                                5
% 2.44/1.02  fd_pure:                                0
% 2.44/1.02  fd_pseudo:                              0
% 2.44/1.02  fd_cond:                                1
% 2.44/1.02  fd_pseudo_cond:                         1
% 2.44/1.02  ac_symbols:                             0
% 2.44/1.02  
% 2.44/1.02  ------ Propositional Solver
% 2.44/1.02  
% 2.44/1.02  prop_solver_calls:                      30
% 2.44/1.02  prop_fast_solver_calls:                 884
% 2.44/1.02  smt_solver_calls:                       0
% 2.44/1.02  smt_fast_solver_calls:                  0
% 2.44/1.02  prop_num_of_clauses:                    2057
% 2.44/1.02  prop_preprocess_simplified:             5528
% 2.44/1.02  prop_fo_subsumed:                       45
% 2.44/1.02  prop_solver_time:                       0.
% 2.44/1.02  smt_solver_time:                        0.
% 2.44/1.02  smt_fast_solver_time:                   0.
% 2.44/1.02  prop_fast_solver_time:                  0.
% 2.44/1.02  prop_unsat_core_time:                   0.
% 2.44/1.02  
% 2.44/1.02  ------ QBF
% 2.44/1.02  
% 2.44/1.02  qbf_q_res:                              0
% 2.44/1.02  qbf_num_tautologies:                    0
% 2.44/1.02  qbf_prep_cycles:                        0
% 2.44/1.02  
% 2.44/1.02  ------ BMC1
% 2.44/1.02  
% 2.44/1.02  bmc1_current_bound:                     -1
% 2.44/1.02  bmc1_last_solved_bound:                 -1
% 2.44/1.02  bmc1_unsat_core_size:                   -1
% 2.44/1.02  bmc1_unsat_core_parents_size:           -1
% 2.44/1.02  bmc1_merge_next_fun:                    0
% 2.44/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.02  
% 2.44/1.02  ------ Instantiation
% 2.44/1.02  
% 2.44/1.02  inst_num_of_clauses:                    649
% 2.44/1.02  inst_num_in_passive:                    118
% 2.44/1.02  inst_num_in_active:                     347
% 2.44/1.02  inst_num_in_unprocessed:                184
% 2.44/1.02  inst_num_of_loops:                      380
% 2.44/1.02  inst_num_of_learning_restarts:          0
% 2.44/1.02  inst_num_moves_active_passive:          29
% 2.44/1.02  inst_lit_activity:                      0
% 2.44/1.02  inst_lit_activity_moves:                0
% 2.44/1.02  inst_num_tautologies:                   0
% 2.44/1.02  inst_num_prop_implied:                  0
% 2.44/1.02  inst_num_existing_simplified:           0
% 2.44/1.02  inst_num_eq_res_simplified:             0
% 2.44/1.02  inst_num_child_elim:                    0
% 2.44/1.02  inst_num_of_dismatching_blockings:      200
% 2.44/1.02  inst_num_of_non_proper_insts:           973
% 2.44/1.02  inst_num_of_duplicates:                 0
% 2.44/1.02  inst_inst_num_from_inst_to_res:         0
% 2.44/1.02  inst_dismatching_checking_time:         0.
% 2.44/1.02  
% 2.44/1.02  ------ Resolution
% 2.44/1.02  
% 2.44/1.02  res_num_of_clauses:                     0
% 2.44/1.02  res_num_in_passive:                     0
% 2.44/1.02  res_num_in_active:                      0
% 2.44/1.02  res_num_of_loops:                       93
% 2.44/1.02  res_forward_subset_subsumed:            85
% 2.44/1.02  res_backward_subset_subsumed:           4
% 2.44/1.02  res_forward_subsumed:                   0
% 2.44/1.02  res_backward_subsumed:                  0
% 2.44/1.02  res_forward_subsumption_resolution:     0
% 2.44/1.02  res_backward_subsumption_resolution:    0
% 2.44/1.02  res_clause_to_clause_subsumption:       890
% 2.44/1.02  res_orphan_elimination:                 0
% 2.44/1.02  res_tautology_del:                      160
% 2.44/1.02  res_num_eq_res_simplified:              0
% 2.44/1.02  res_num_sel_changes:                    0
% 2.44/1.02  res_moves_from_active_to_pass:          0
% 2.44/1.02  
% 2.44/1.02  ------ Superposition
% 2.44/1.02  
% 2.44/1.02  sup_time_total:                         0.
% 2.44/1.02  sup_time_generating:                    0.
% 2.44/1.02  sup_time_sim_full:                      0.
% 2.44/1.02  sup_time_sim_immed:                     0.
% 2.44/1.02  
% 2.44/1.02  sup_num_of_clauses:                     90
% 2.44/1.02  sup_num_in_active:                      50
% 2.44/1.02  sup_num_in_passive:                     40
% 2.44/1.02  sup_num_of_loops:                       75
% 2.44/1.02  sup_fw_superposition:                   110
% 2.44/1.02  sup_bw_superposition:                   78
% 2.44/1.02  sup_immediate_simplified:               39
% 2.44/1.02  sup_given_eliminated:                   0
% 2.44/1.02  comparisons_done:                       0
% 2.44/1.02  comparisons_avoided:                    0
% 2.44/1.02  
% 2.44/1.02  ------ Simplifications
% 2.44/1.02  
% 2.44/1.02  
% 2.44/1.02  sim_fw_subset_subsumed:                 17
% 2.44/1.02  sim_bw_subset_subsumed:                 9
% 2.44/1.02  sim_fw_subsumed:                        23
% 2.44/1.02  sim_bw_subsumed:                        4
% 2.44/1.02  sim_fw_subsumption_res:                 1
% 2.44/1.02  sim_bw_subsumption_res:                 0
% 2.44/1.02  sim_tautology_del:                      13
% 2.44/1.02  sim_eq_tautology_del:                   9
% 2.44/1.02  sim_eq_res_simp:                        0
% 2.44/1.02  sim_fw_demodulated:                     0
% 2.44/1.02  sim_bw_demodulated:                     24
% 2.44/1.02  sim_light_normalised:                   4
% 2.44/1.02  sim_joinable_taut:                      0
% 2.44/1.02  sim_joinable_simp:                      0
% 2.44/1.02  sim_ac_normalised:                      0
% 2.44/1.02  sim_smt_subsumption:                    0
% 2.44/1.02  
%------------------------------------------------------------------------------
