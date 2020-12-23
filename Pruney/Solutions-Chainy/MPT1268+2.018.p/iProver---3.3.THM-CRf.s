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
% DateTime   : Thu Dec  3 12:15:05 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  168 (2798 expanded)
%              Number of clauses        :  110 ( 733 expanded)
%              Number of leaves         :   14 ( 666 expanded)
%              Depth                    :   23
%              Number of atoms          :  574 (23126 expanded)
%              Number of equality atoms :  217 (4149 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f35,f34,f33])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1555,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_302,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_303,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_20])).

cnf(c_308,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_307])).

cnf(c_1553,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_2455,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1553])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1562,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1556,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2180,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1556])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1762,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_1883,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1882])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1783,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2134,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_2135,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2134])).

cnf(c_3871,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | v2_tops_1(sK1,sK0) = iProver_top
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2180,c_24,c_1883,c_2135])).

cnf(c_3872,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3871])).

cnf(c_3881,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2455,c_3872])).

cnf(c_12,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_338,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_339,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_1696,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_1697,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1696])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_1699,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_1700,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_7398,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3881,c_24,c_1697,c_1700])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_323,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_324,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_1552,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_2638,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1552])).

cnf(c_7403,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7398,c_2638])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1565,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1557,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_353,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_354,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_1550,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_1938,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1550])).

cnf(c_28,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_403,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1))
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_354])).

cnf(c_404,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_405,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_3395,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1938,c_28,c_405])).

cnf(c_3405,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_3395])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3567,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3405,c_29])).

cnf(c_3568,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3567])).

cnf(c_1563,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3573,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3568,c_1563])).

cnf(c_5783,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3573,c_24,c_1697,c_1700,c_3881])).

cnf(c_5791,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1565,c_5783])).

cnf(c_7569,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7403,c_5791])).

cnf(c_1549,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_1846,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1549])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1566,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2857,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_1566])).

cnf(c_3404,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_3395])).

cnf(c_3538,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3404,c_1565])).

cnf(c_3541,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3538,c_1566])).

cnf(c_5430,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2857,c_24,c_1697,c_1700,c_1846,c_3541,c_3881])).

cnf(c_2637,plain,
    ( k1_tops_1(sK0,sK2) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | v2_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1552])).

cnf(c_5437,plain,
    ( sK2 = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | v2_tops_1(sK2,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5430,c_2637])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_339])).

cnf(c_636,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_638,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_636,c_19])).

cnf(c_5468,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v2_tops_1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5437,c_19,c_24,c_636,c_1697,c_1700,c_2638,c_3881])).

cnf(c_5472,plain,
    ( v2_tops_1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5468,c_19,c_24,c_636,c_1697,c_1700,c_2638,c_3881,c_5437])).

cnf(c_1551,plain,
    ( k1_tops_1(sK0,X0) != k1_xboole_0
    | v2_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_5452,plain,
    ( sK2 != k1_xboole_0
    | v2_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5430,c_1551])).

cnf(c_1707,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5338,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_5339,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5338])).

cnf(c_1561,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2092,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1561])).

cnf(c_2895,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2092,c_1563])).

cnf(c_5301,plain,
    ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2895,c_24,c_1697,c_1700,c_3881])).

cnf(c_5309,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1565,c_5301])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_287,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 != X2
    | k4_xboole_0(X3,X1) != X4
    | k3_xboole_0(X2,X4) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_288,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_1554,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_2665,plain,
    ( k3_xboole_0(sK2,k4_xboole_0(X0,u1_struct_0(sK0))) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2092,c_1554])).

cnf(c_5055,plain,
    ( k3_xboole_0(sK2,k4_xboole_0(X0,u1_struct_0(sK0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2665,c_24,c_1697,c_1700,c_3881])).

cnf(c_4,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1564,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2853,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1564,c_1566])).

cnf(c_5059,plain,
    ( k3_xboole_0(sK2,k4_xboole_0(X0,u1_struct_0(sK0))) = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5055,c_2853])).

cnf(c_5065,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5059,c_5055])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7569,c_5472,c_5452,c_5339,c_5309,c_5065])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.51/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/0.99  
% 2.51/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.51/0.99  
% 2.51/0.99  ------  iProver source info
% 2.51/0.99  
% 2.51/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.51/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.51/0.99  git: non_committed_changes: false
% 2.51/0.99  git: last_make_outside_of_git: false
% 2.51/0.99  
% 2.51/0.99  ------ 
% 2.51/0.99  
% 2.51/0.99  ------ Input Options
% 2.51/0.99  
% 2.51/0.99  --out_options                           all
% 2.51/0.99  --tptp_safe_out                         true
% 2.51/0.99  --problem_path                          ""
% 2.51/0.99  --include_path                          ""
% 2.51/0.99  --clausifier                            res/vclausify_rel
% 2.51/0.99  --clausifier_options                    --mode clausify
% 2.51/0.99  --stdin                                 false
% 2.51/0.99  --stats_out                             all
% 2.51/0.99  
% 2.51/0.99  ------ General Options
% 2.51/0.99  
% 2.51/0.99  --fof                                   false
% 2.51/0.99  --time_out_real                         305.
% 2.51/0.99  --time_out_virtual                      -1.
% 2.51/0.99  --symbol_type_check                     false
% 2.51/0.99  --clausify_out                          false
% 2.51/0.99  --sig_cnt_out                           false
% 2.51/0.99  --trig_cnt_out                          false
% 2.51/0.99  --trig_cnt_out_tolerance                1.
% 2.51/0.99  --trig_cnt_out_sk_spl                   false
% 2.51/0.99  --abstr_cl_out                          false
% 2.51/0.99  
% 2.51/0.99  ------ Global Options
% 2.51/0.99  
% 2.51/0.99  --schedule                              default
% 2.51/0.99  --add_important_lit                     false
% 2.51/0.99  --prop_solver_per_cl                    1000
% 2.51/0.99  --min_unsat_core                        false
% 2.51/0.99  --soft_assumptions                      false
% 2.51/0.99  --soft_lemma_size                       3
% 2.51/0.99  --prop_impl_unit_size                   0
% 2.51/0.99  --prop_impl_unit                        []
% 2.51/0.99  --share_sel_clauses                     true
% 2.51/0.99  --reset_solvers                         false
% 2.51/0.99  --bc_imp_inh                            [conj_cone]
% 2.51/0.99  --conj_cone_tolerance                   3.
% 2.51/0.99  --extra_neg_conj                        none
% 2.51/0.99  --large_theory_mode                     true
% 2.51/0.99  --prolific_symb_bound                   200
% 2.51/0.99  --lt_threshold                          2000
% 2.51/0.99  --clause_weak_htbl                      true
% 2.51/0.99  --gc_record_bc_elim                     false
% 2.51/0.99  
% 2.51/0.99  ------ Preprocessing Options
% 2.51/0.99  
% 2.51/0.99  --preprocessing_flag                    true
% 2.51/0.99  --time_out_prep_mult                    0.1
% 2.51/0.99  --splitting_mode                        input
% 2.51/0.99  --splitting_grd                         true
% 2.51/0.99  --splitting_cvd                         false
% 2.51/0.99  --splitting_cvd_svl                     false
% 2.51/0.99  --splitting_nvd                         32
% 2.51/0.99  --sub_typing                            true
% 2.51/0.99  --prep_gs_sim                           true
% 2.51/0.99  --prep_unflatten                        true
% 2.51/0.99  --prep_res_sim                          true
% 2.51/0.99  --prep_upred                            true
% 2.51/0.99  --prep_sem_filter                       exhaustive
% 2.51/0.99  --prep_sem_filter_out                   false
% 2.51/0.99  --pred_elim                             true
% 2.51/0.99  --res_sim_input                         true
% 2.51/0.99  --eq_ax_congr_red                       true
% 2.51/0.99  --pure_diseq_elim                       true
% 2.51/0.99  --brand_transform                       false
% 2.51/0.99  --non_eq_to_eq                          false
% 2.51/0.99  --prep_def_merge                        true
% 2.51/0.99  --prep_def_merge_prop_impl              false
% 2.51/0.99  --prep_def_merge_mbd                    true
% 2.51/0.99  --prep_def_merge_tr_red                 false
% 2.51/0.99  --prep_def_merge_tr_cl                  false
% 2.51/0.99  --smt_preprocessing                     true
% 2.51/0.99  --smt_ac_axioms                         fast
% 2.51/0.99  --preprocessed_out                      false
% 2.51/0.99  --preprocessed_stats                    false
% 2.51/0.99  
% 2.51/0.99  ------ Abstraction refinement Options
% 2.51/0.99  
% 2.51/0.99  --abstr_ref                             []
% 2.51/0.99  --abstr_ref_prep                        false
% 2.51/0.99  --abstr_ref_until_sat                   false
% 2.51/0.99  --abstr_ref_sig_restrict                funpre
% 2.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/0.99  --abstr_ref_under                       []
% 2.51/0.99  
% 2.51/0.99  ------ SAT Options
% 2.51/0.99  
% 2.51/0.99  --sat_mode                              false
% 2.51/0.99  --sat_fm_restart_options                ""
% 2.51/0.99  --sat_gr_def                            false
% 2.51/0.99  --sat_epr_types                         true
% 2.51/0.99  --sat_non_cyclic_types                  false
% 2.51/0.99  --sat_finite_models                     false
% 2.51/0.99  --sat_fm_lemmas                         false
% 2.51/0.99  --sat_fm_prep                           false
% 2.51/0.99  --sat_fm_uc_incr                        true
% 2.51/0.99  --sat_out_model                         small
% 2.51/0.99  --sat_out_clauses                       false
% 2.51/0.99  
% 2.51/0.99  ------ QBF Options
% 2.51/0.99  
% 2.51/0.99  --qbf_mode                              false
% 2.51/0.99  --qbf_elim_univ                         false
% 2.51/0.99  --qbf_dom_inst                          none
% 2.51/0.99  --qbf_dom_pre_inst                      false
% 2.51/0.99  --qbf_sk_in                             false
% 2.51/0.99  --qbf_pred_elim                         true
% 2.51/0.99  --qbf_split                             512
% 2.51/0.99  
% 2.51/0.99  ------ BMC1 Options
% 2.51/0.99  
% 2.51/0.99  --bmc1_incremental                      false
% 2.51/0.99  --bmc1_axioms                           reachable_all
% 2.51/0.99  --bmc1_min_bound                        0
% 2.51/0.99  --bmc1_max_bound                        -1
% 2.51/0.99  --bmc1_max_bound_default                -1
% 2.51/0.99  --bmc1_symbol_reachability              true
% 2.51/0.99  --bmc1_property_lemmas                  false
% 2.51/0.99  --bmc1_k_induction                      false
% 2.51/0.99  --bmc1_non_equiv_states                 false
% 2.51/0.99  --bmc1_deadlock                         false
% 2.51/0.99  --bmc1_ucm                              false
% 2.51/0.99  --bmc1_add_unsat_core                   none
% 2.51/0.99  --bmc1_unsat_core_children              false
% 2.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/0.99  --bmc1_out_stat                         full
% 2.51/0.99  --bmc1_ground_init                      false
% 2.51/0.99  --bmc1_pre_inst_next_state              false
% 2.51/0.99  --bmc1_pre_inst_state                   false
% 2.51/0.99  --bmc1_pre_inst_reach_state             false
% 2.51/0.99  --bmc1_out_unsat_core                   false
% 2.51/0.99  --bmc1_aig_witness_out                  false
% 2.51/0.99  --bmc1_verbose                          false
% 2.51/0.99  --bmc1_dump_clauses_tptp                false
% 2.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.51/0.99  --bmc1_dump_file                        -
% 2.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.51/0.99  --bmc1_ucm_extend_mode                  1
% 2.51/0.99  --bmc1_ucm_init_mode                    2
% 2.51/0.99  --bmc1_ucm_cone_mode                    none
% 2.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.51/0.99  --bmc1_ucm_relax_model                  4
% 2.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/0.99  --bmc1_ucm_layered_model                none
% 2.51/0.99  --bmc1_ucm_max_lemma_size               10
% 2.51/0.99  
% 2.51/0.99  ------ AIG Options
% 2.51/0.99  
% 2.51/0.99  --aig_mode                              false
% 2.51/0.99  
% 2.51/0.99  ------ Instantiation Options
% 2.51/0.99  
% 2.51/0.99  --instantiation_flag                    true
% 2.51/0.99  --inst_sos_flag                         false
% 2.51/0.99  --inst_sos_phase                        true
% 2.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/0.99  --inst_lit_sel_side                     num_symb
% 2.51/0.99  --inst_solver_per_active                1400
% 2.51/0.99  --inst_solver_calls_frac                1.
% 2.51/0.99  --inst_passive_queue_type               priority_queues
% 2.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/0.99  --inst_passive_queues_freq              [25;2]
% 2.51/0.99  --inst_dismatching                      true
% 2.51/0.99  --inst_eager_unprocessed_to_passive     true
% 2.51/0.99  --inst_prop_sim_given                   true
% 2.51/0.99  --inst_prop_sim_new                     false
% 2.51/0.99  --inst_subs_new                         false
% 2.51/0.99  --inst_eq_res_simp                      false
% 2.51/0.99  --inst_subs_given                       false
% 2.51/0.99  --inst_orphan_elimination               true
% 2.51/0.99  --inst_learning_loop_flag               true
% 2.51/0.99  --inst_learning_start                   3000
% 2.51/0.99  --inst_learning_factor                  2
% 2.51/0.99  --inst_start_prop_sim_after_learn       3
% 2.51/0.99  --inst_sel_renew                        solver
% 2.51/0.99  --inst_lit_activity_flag                true
% 2.51/0.99  --inst_restr_to_given                   false
% 2.51/0.99  --inst_activity_threshold               500
% 2.51/0.99  --inst_out_proof                        true
% 2.51/0.99  
% 2.51/0.99  ------ Resolution Options
% 2.51/0.99  
% 2.51/0.99  --resolution_flag                       true
% 2.51/0.99  --res_lit_sel                           adaptive
% 2.51/0.99  --res_lit_sel_side                      none
% 2.51/0.99  --res_ordering                          kbo
% 2.51/0.99  --res_to_prop_solver                    active
% 2.51/0.99  --res_prop_simpl_new                    false
% 2.51/0.99  --res_prop_simpl_given                  true
% 2.51/0.99  --res_passive_queue_type                priority_queues
% 2.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/0.99  --res_passive_queues_freq               [15;5]
% 2.51/0.99  --res_forward_subs                      full
% 2.51/0.99  --res_backward_subs                     full
% 2.51/0.99  --res_forward_subs_resolution           true
% 2.51/0.99  --res_backward_subs_resolution          true
% 2.51/0.99  --res_orphan_elimination                true
% 2.51/0.99  --res_time_limit                        2.
% 2.51/0.99  --res_out_proof                         true
% 2.51/0.99  
% 2.51/0.99  ------ Superposition Options
% 2.51/0.99  
% 2.51/0.99  --superposition_flag                    true
% 2.51/0.99  --sup_passive_queue_type                priority_queues
% 2.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.51/0.99  --demod_completeness_check              fast
% 2.51/0.99  --demod_use_ground                      true
% 2.51/0.99  --sup_to_prop_solver                    passive
% 2.51/0.99  --sup_prop_simpl_new                    true
% 2.51/0.99  --sup_prop_simpl_given                  true
% 2.51/0.99  --sup_fun_splitting                     false
% 2.51/0.99  --sup_smt_interval                      50000
% 2.51/0.99  
% 2.51/0.99  ------ Superposition Simplification Setup
% 2.51/0.99  
% 2.51/0.99  --sup_indices_passive                   []
% 2.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.99  --sup_full_bw                           [BwDemod]
% 2.51/0.99  --sup_immed_triv                        [TrivRules]
% 2.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.99  --sup_immed_bw_main                     []
% 2.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.99  
% 2.51/0.99  ------ Combination Options
% 2.51/0.99  
% 2.51/0.99  --comb_res_mult                         3
% 2.51/0.99  --comb_sup_mult                         2
% 2.51/0.99  --comb_inst_mult                        10
% 2.51/0.99  
% 2.51/0.99  ------ Debug Options
% 2.51/0.99  
% 2.51/0.99  --dbg_backtrace                         false
% 2.51/0.99  --dbg_dump_prop_clauses                 false
% 2.51/0.99  --dbg_dump_prop_clauses_file            -
% 2.51/0.99  --dbg_out_stat                          false
% 2.51/0.99  ------ Parsing...
% 2.51/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.51/0.99  
% 2.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.51/0.99  
% 2.51/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.51/0.99  
% 2.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.51/0.99  ------ Proving...
% 2.51/0.99  ------ Problem Properties 
% 2.51/0.99  
% 2.51/0.99  
% 2.51/0.99  clauses                                 18
% 2.51/0.99  conjectures                             6
% 2.51/0.99  EPR                                     6
% 2.51/0.99  Horn                                    17
% 2.51/0.99  unary                                   3
% 2.51/0.99  binary                                  9
% 2.51/0.99  lits                                    43
% 2.51/0.99  lits eq                                 6
% 2.51/0.99  fd_pure                                 0
% 2.51/0.99  fd_pseudo                               0
% 2.51/0.99  fd_cond                                 1
% 2.51/0.99  fd_pseudo_cond                          1
% 2.51/0.99  AC symbols                              0
% 2.51/0.99  
% 2.51/0.99  ------ Schedule dynamic 5 is on 
% 2.51/0.99  
% 2.51/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.51/0.99  
% 2.51/0.99  
% 2.51/0.99  ------ 
% 2.51/0.99  Current options:
% 2.51/0.99  ------ 
% 2.51/0.99  
% 2.51/0.99  ------ Input Options
% 2.51/0.99  
% 2.51/0.99  --out_options                           all
% 2.51/0.99  --tptp_safe_out                         true
% 2.51/0.99  --problem_path                          ""
% 2.51/0.99  --include_path                          ""
% 2.51/0.99  --clausifier                            res/vclausify_rel
% 2.51/0.99  --clausifier_options                    --mode clausify
% 2.51/0.99  --stdin                                 false
% 2.51/0.99  --stats_out                             all
% 2.51/0.99  
% 2.51/0.99  ------ General Options
% 2.51/0.99  
% 2.51/0.99  --fof                                   false
% 2.51/0.99  --time_out_real                         305.
% 2.51/0.99  --time_out_virtual                      -1.
% 2.51/0.99  --symbol_type_check                     false
% 2.51/0.99  --clausify_out                          false
% 2.51/0.99  --sig_cnt_out                           false
% 2.51/0.99  --trig_cnt_out                          false
% 2.51/0.99  --trig_cnt_out_tolerance                1.
% 2.51/0.99  --trig_cnt_out_sk_spl                   false
% 2.51/0.99  --abstr_cl_out                          false
% 2.51/0.99  
% 2.51/0.99  ------ Global Options
% 2.51/0.99  
% 2.51/0.99  --schedule                              default
% 2.51/0.99  --add_important_lit                     false
% 2.51/0.99  --prop_solver_per_cl                    1000
% 2.51/0.99  --min_unsat_core                        false
% 2.51/0.99  --soft_assumptions                      false
% 2.51/0.99  --soft_lemma_size                       3
% 2.51/0.99  --prop_impl_unit_size                   0
% 2.51/0.99  --prop_impl_unit                        []
% 2.51/0.99  --share_sel_clauses                     true
% 2.51/0.99  --reset_solvers                         false
% 2.51/0.99  --bc_imp_inh                            [conj_cone]
% 2.51/0.99  --conj_cone_tolerance                   3.
% 2.51/0.99  --extra_neg_conj                        none
% 2.51/0.99  --large_theory_mode                     true
% 2.51/0.99  --prolific_symb_bound                   200
% 2.51/0.99  --lt_threshold                          2000
% 2.51/0.99  --clause_weak_htbl                      true
% 2.51/0.99  --gc_record_bc_elim                     false
% 2.51/0.99  
% 2.51/0.99  ------ Preprocessing Options
% 2.51/0.99  
% 2.51/0.99  --preprocessing_flag                    true
% 2.51/0.99  --time_out_prep_mult                    0.1
% 2.51/0.99  --splitting_mode                        input
% 2.51/0.99  --splitting_grd                         true
% 2.51/0.99  --splitting_cvd                         false
% 2.51/0.99  --splitting_cvd_svl                     false
% 2.51/0.99  --splitting_nvd                         32
% 2.51/0.99  --sub_typing                            true
% 2.51/0.99  --prep_gs_sim                           true
% 2.51/0.99  --prep_unflatten                        true
% 2.51/0.99  --prep_res_sim                          true
% 2.51/0.99  --prep_upred                            true
% 2.51/0.99  --prep_sem_filter                       exhaustive
% 2.51/0.99  --prep_sem_filter_out                   false
% 2.51/0.99  --pred_elim                             true
% 2.51/0.99  --res_sim_input                         true
% 2.51/0.99  --eq_ax_congr_red                       true
% 2.51/0.99  --pure_diseq_elim                       true
% 2.51/0.99  --brand_transform                       false
% 2.51/0.99  --non_eq_to_eq                          false
% 2.51/0.99  --prep_def_merge                        true
% 2.51/0.99  --prep_def_merge_prop_impl              false
% 2.51/0.99  --prep_def_merge_mbd                    true
% 2.51/0.99  --prep_def_merge_tr_red                 false
% 2.51/0.99  --prep_def_merge_tr_cl                  false
% 2.51/0.99  --smt_preprocessing                     true
% 2.51/0.99  --smt_ac_axioms                         fast
% 2.51/0.99  --preprocessed_out                      false
% 2.51/0.99  --preprocessed_stats                    false
% 2.51/0.99  
% 2.51/0.99  ------ Abstraction refinement Options
% 2.51/0.99  
% 2.51/0.99  --abstr_ref                             []
% 2.51/0.99  --abstr_ref_prep                        false
% 2.51/0.99  --abstr_ref_until_sat                   false
% 2.51/0.99  --abstr_ref_sig_restrict                funpre
% 2.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/0.99  --abstr_ref_under                       []
% 2.51/0.99  
% 2.51/0.99  ------ SAT Options
% 2.51/0.99  
% 2.51/0.99  --sat_mode                              false
% 2.51/0.99  --sat_fm_restart_options                ""
% 2.51/0.99  --sat_gr_def                            false
% 2.51/0.99  --sat_epr_types                         true
% 2.51/0.99  --sat_non_cyclic_types                  false
% 2.51/0.99  --sat_finite_models                     false
% 2.51/0.99  --sat_fm_lemmas                         false
% 2.51/0.99  --sat_fm_prep                           false
% 2.51/0.99  --sat_fm_uc_incr                        true
% 2.51/0.99  --sat_out_model                         small
% 2.51/0.99  --sat_out_clauses                       false
% 2.51/0.99  
% 2.51/0.99  ------ QBF Options
% 2.51/0.99  
% 2.51/0.99  --qbf_mode                              false
% 2.51/0.99  --qbf_elim_univ                         false
% 2.51/0.99  --qbf_dom_inst                          none
% 2.51/0.99  --qbf_dom_pre_inst                      false
% 2.51/0.99  --qbf_sk_in                             false
% 2.51/0.99  --qbf_pred_elim                         true
% 2.51/0.99  --qbf_split                             512
% 2.51/0.99  
% 2.51/0.99  ------ BMC1 Options
% 2.51/0.99  
% 2.51/0.99  --bmc1_incremental                      false
% 2.51/0.99  --bmc1_axioms                           reachable_all
% 2.51/0.99  --bmc1_min_bound                        0
% 2.51/0.99  --bmc1_max_bound                        -1
% 2.51/0.99  --bmc1_max_bound_default                -1
% 2.51/0.99  --bmc1_symbol_reachability              true
% 2.51/0.99  --bmc1_property_lemmas                  false
% 2.51/0.99  --bmc1_k_induction                      false
% 2.51/0.99  --bmc1_non_equiv_states                 false
% 2.51/0.99  --bmc1_deadlock                         false
% 2.51/0.99  --bmc1_ucm                              false
% 2.51/0.99  --bmc1_add_unsat_core                   none
% 2.51/0.99  --bmc1_unsat_core_children              false
% 2.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/0.99  --bmc1_out_stat                         full
% 2.51/0.99  --bmc1_ground_init                      false
% 2.51/0.99  --bmc1_pre_inst_next_state              false
% 2.51/0.99  --bmc1_pre_inst_state                   false
% 2.51/0.99  --bmc1_pre_inst_reach_state             false
% 2.51/0.99  --bmc1_out_unsat_core                   false
% 2.51/0.99  --bmc1_aig_witness_out                  false
% 2.51/0.99  --bmc1_verbose                          false
% 2.51/0.99  --bmc1_dump_clauses_tptp                false
% 2.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.51/0.99  --bmc1_dump_file                        -
% 2.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.51/0.99  --bmc1_ucm_extend_mode                  1
% 2.51/0.99  --bmc1_ucm_init_mode                    2
% 2.51/0.99  --bmc1_ucm_cone_mode                    none
% 2.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.51/0.99  --bmc1_ucm_relax_model                  4
% 2.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/0.99  --bmc1_ucm_layered_model                none
% 2.51/0.99  --bmc1_ucm_max_lemma_size               10
% 2.51/0.99  
% 2.51/0.99  ------ AIG Options
% 2.51/0.99  
% 2.51/0.99  --aig_mode                              false
% 2.51/0.99  
% 2.51/0.99  ------ Instantiation Options
% 2.51/0.99  
% 2.51/0.99  --instantiation_flag                    true
% 2.51/0.99  --inst_sos_flag                         false
% 2.51/0.99  --inst_sos_phase                        true
% 2.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/0.99  --inst_lit_sel_side                     none
% 2.51/0.99  --inst_solver_per_active                1400
% 2.51/0.99  --inst_solver_calls_frac                1.
% 2.51/0.99  --inst_passive_queue_type               priority_queues
% 2.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/0.99  --inst_passive_queues_freq              [25;2]
% 2.51/0.99  --inst_dismatching                      true
% 2.51/0.99  --inst_eager_unprocessed_to_passive     true
% 2.51/0.99  --inst_prop_sim_given                   true
% 2.51/0.99  --inst_prop_sim_new                     false
% 2.51/0.99  --inst_subs_new                         false
% 2.51/0.99  --inst_eq_res_simp                      false
% 2.51/0.99  --inst_subs_given                       false
% 2.51/0.99  --inst_orphan_elimination               true
% 2.51/0.99  --inst_learning_loop_flag               true
% 2.51/0.99  --inst_learning_start                   3000
% 2.51/0.99  --inst_learning_factor                  2
% 2.51/0.99  --inst_start_prop_sim_after_learn       3
% 2.51/0.99  --inst_sel_renew                        solver
% 2.51/0.99  --inst_lit_activity_flag                true
% 2.51/0.99  --inst_restr_to_given                   false
% 2.51/0.99  --inst_activity_threshold               500
% 2.51/0.99  --inst_out_proof                        true
% 2.51/0.99  
% 2.51/0.99  ------ Resolution Options
% 2.51/0.99  
% 2.51/0.99  --resolution_flag                       false
% 2.51/0.99  --res_lit_sel                           adaptive
% 2.51/0.99  --res_lit_sel_side                      none
% 2.51/0.99  --res_ordering                          kbo
% 2.51/0.99  --res_to_prop_solver                    active
% 2.51/0.99  --res_prop_simpl_new                    false
% 2.51/0.99  --res_prop_simpl_given                  true
% 2.51/0.99  --res_passive_queue_type                priority_queues
% 2.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/0.99  --res_passive_queues_freq               [15;5]
% 2.51/0.99  --res_forward_subs                      full
% 2.51/0.99  --res_backward_subs                     full
% 2.51/0.99  --res_forward_subs_resolution           true
% 2.51/0.99  --res_backward_subs_resolution          true
% 2.51/0.99  --res_orphan_elimination                true
% 2.51/0.99  --res_time_limit                        2.
% 2.51/0.99  --res_out_proof                         true
% 2.51/0.99  
% 2.51/0.99  ------ Superposition Options
% 2.51/0.99  
% 2.51/0.99  --superposition_flag                    true
% 2.51/0.99  --sup_passive_queue_type                priority_queues
% 2.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.51/0.99  --demod_completeness_check              fast
% 2.51/0.99  --demod_use_ground                      true
% 2.51/0.99  --sup_to_prop_solver                    passive
% 2.51/0.99  --sup_prop_simpl_new                    true
% 2.51/0.99  --sup_prop_simpl_given                  true
% 2.51/0.99  --sup_fun_splitting                     false
% 2.51/0.99  --sup_smt_interval                      50000
% 2.51/0.99  
% 2.51/0.99  ------ Superposition Simplification Setup
% 2.51/0.99  
% 2.51/0.99  --sup_indices_passive                   []
% 2.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.99  --sup_full_bw                           [BwDemod]
% 2.51/0.99  --sup_immed_triv                        [TrivRules]
% 2.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.99  --sup_immed_bw_main                     []
% 2.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.99  
% 2.51/0.99  ------ Combination Options
% 2.51/0.99  
% 2.51/0.99  --comb_res_mult                         3
% 2.51/0.99  --comb_sup_mult                         2
% 2.51/0.99  --comb_inst_mult                        10
% 2.51/0.99  
% 2.51/0.99  ------ Debug Options
% 2.51/0.99  
% 2.51/0.99  --dbg_backtrace                         false
% 2.51/0.99  --dbg_dump_prop_clauses                 false
% 2.51/0.99  --dbg_dump_prop_clauses_file            -
% 2.51/0.99  --dbg_out_stat                          false
% 2.51/0.99  
% 2.51/0.99  
% 2.51/0.99  
% 2.51/0.99  
% 2.51/0.99  ------ Proving...
% 2.51/0.99  
% 2.51/0.99  
% 2.51/0.99  % SZS status Theorem for theBenchmark.p
% 2.51/0.99  
% 2.51/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.51/0.99  
% 2.51/0.99  fof(f11,conjecture,(
% 2.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.99  
% 2.51/0.99  fof(f12,negated_conjecture,(
% 2.51/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.51/0.99    inference(negated_conjecture,[],[f11])).
% 2.51/0.99  
% 2.51/0.99  fof(f24,plain,(
% 2.51/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.51/0.99    inference(ennf_transformation,[],[f12])).
% 2.51/0.99  
% 2.51/0.99  fof(f25,plain,(
% 2.51/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.51/0.99    inference(flattening,[],[f24])).
% 2.51/0.99  
% 2.51/0.99  fof(f30,plain,(
% 2.51/0.99    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.51/0.99    inference(nnf_transformation,[],[f25])).
% 2.51/0.99  
% 2.51/0.99  fof(f31,plain,(
% 2.51/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.51/0.99    inference(flattening,[],[f30])).
% 2.51/0.99  
% 2.51/0.99  fof(f32,plain,(
% 2.51/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.51/0.99    inference(rectify,[],[f31])).
% 2.51/0.99  
% 2.51/0.99  fof(f35,plain,(
% 2.51/0.99    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.51/0.99    introduced(choice_axiom,[])).
% 2.51/0.99  
% 2.51/0.99  fof(f34,plain,(
% 2.51/0.99    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.51/0.99    introduced(choice_axiom,[])).
% 2.51/0.99  
% 2.51/0.99  fof(f33,plain,(
% 2.51/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.51/1.00    introduced(choice_axiom,[])).
% 2.51/1.00  
% 2.51/1.00  fof(f36,plain,(
% 2.51/1.00    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f35,f34,f33])).
% 2.51/1.00  
% 2.51/1.00  fof(f53,plain,(
% 2.51/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.51/1.00    inference(cnf_transformation,[],[f36])).
% 2.51/1.00  
% 2.51/1.00  fof(f7,axiom,(
% 2.51/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f18,plain,(
% 2.51/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.51/1.00    inference(ennf_transformation,[],[f7])).
% 2.51/1.00  
% 2.51/1.00  fof(f19,plain,(
% 2.51/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.51/1.00    inference(flattening,[],[f18])).
% 2.51/1.00  
% 2.51/1.00  fof(f46,plain,(
% 2.51/1.00    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f19])).
% 2.51/1.00  
% 2.51/1.00  fof(f51,plain,(
% 2.51/1.00    v2_pre_topc(sK0)),
% 2.51/1.00    inference(cnf_transformation,[],[f36])).
% 2.51/1.00  
% 2.51/1.00  fof(f52,plain,(
% 2.51/1.00    l1_pre_topc(sK0)),
% 2.51/1.00    inference(cnf_transformation,[],[f36])).
% 2.51/1.00  
% 2.51/1.00  fof(f6,axiom,(
% 2.51/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f28,plain,(
% 2.51/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.51/1.00    inference(nnf_transformation,[],[f6])).
% 2.51/1.00  
% 2.51/1.00  fof(f45,plain,(
% 2.51/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f28])).
% 2.51/1.00  
% 2.51/1.00  fof(f54,plain,(
% 2.51/1.00    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f36])).
% 2.51/1.00  
% 2.51/1.00  fof(f44,plain,(
% 2.51/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.51/1.00    inference(cnf_transformation,[],[f28])).
% 2.51/1.00  
% 2.51/1.00  fof(f4,axiom,(
% 2.51/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f15,plain,(
% 2.51/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.51/1.00    inference(ennf_transformation,[],[f4])).
% 2.51/1.00  
% 2.51/1.00  fof(f16,plain,(
% 2.51/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.51/1.00    inference(flattening,[],[f15])).
% 2.51/1.00  
% 2.51/1.00  fof(f42,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f16])).
% 2.51/1.00  
% 2.51/1.00  fof(f10,axiom,(
% 2.51/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f23,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.51/1.00    inference(ennf_transformation,[],[f10])).
% 2.51/1.00  
% 2.51/1.00  fof(f29,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.51/1.00    inference(nnf_transformation,[],[f23])).
% 2.51/1.00  
% 2.51/1.00  fof(f50,plain,(
% 2.51/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f29])).
% 2.51/1.00  
% 2.51/1.00  fof(f8,axiom,(
% 2.51/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f20,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.51/1.00    inference(ennf_transformation,[],[f8])).
% 2.51/1.00  
% 2.51/1.00  fof(f47,plain,(
% 2.51/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f20])).
% 2.51/1.00  
% 2.51/1.00  fof(f49,plain,(
% 2.51/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f29])).
% 2.51/1.00  
% 2.51/1.00  fof(f2,axiom,(
% 2.51/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f26,plain,(
% 2.51/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.51/1.00    inference(nnf_transformation,[],[f2])).
% 2.51/1.00  
% 2.51/1.00  fof(f27,plain,(
% 2.51/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.51/1.00    inference(flattening,[],[f26])).
% 2.51/1.00  
% 2.51/1.00  fof(f38,plain,(
% 2.51/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.51/1.00    inference(cnf_transformation,[],[f27])).
% 2.51/1.00  
% 2.51/1.00  fof(f60,plain,(
% 2.51/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.51/1.00    inference(equality_resolution,[],[f38])).
% 2.51/1.00  
% 2.51/1.00  fof(f55,plain,(
% 2.51/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 2.51/1.00    inference(cnf_transformation,[],[f36])).
% 2.51/1.00  
% 2.51/1.00  fof(f9,axiom,(
% 2.51/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f21,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.51/1.00    inference(ennf_transformation,[],[f9])).
% 2.51/1.00  
% 2.51/1.00  fof(f22,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.51/1.00    inference(flattening,[],[f21])).
% 2.51/1.00  
% 2.51/1.00  fof(f48,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f22])).
% 2.51/1.00  
% 2.51/1.00  fof(f57,plain,(
% 2.51/1.00    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 2.51/1.00    inference(cnf_transformation,[],[f36])).
% 2.51/1.00  
% 2.51/1.00  fof(f56,plain,(
% 2.51/1.00    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.51/1.00    inference(cnf_transformation,[],[f36])).
% 2.51/1.00  
% 2.51/1.00  fof(f40,plain,(
% 2.51/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f27])).
% 2.51/1.00  
% 2.51/1.00  fof(f58,plain,(
% 2.51/1.00    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 2.51/1.00    inference(cnf_transformation,[],[f36])).
% 2.51/1.00  
% 2.51/1.00  fof(f1,axiom,(
% 2.51/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f13,plain,(
% 2.51/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.51/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 2.51/1.00  
% 2.51/1.00  fof(f14,plain,(
% 2.51/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.51/1.00    inference(ennf_transformation,[],[f13])).
% 2.51/1.00  
% 2.51/1.00  fof(f37,plain,(
% 2.51/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f14])).
% 2.51/1.00  
% 2.51/1.00  fof(f5,axiom,(
% 2.51/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f17,plain,(
% 2.51/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.51/1.00    inference(ennf_transformation,[],[f5])).
% 2.51/1.00  
% 2.51/1.00  fof(f43,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f17])).
% 2.51/1.00  
% 2.51/1.00  fof(f3,axiom,(
% 2.51/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f41,plain,(
% 2.51/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f3])).
% 2.51/1.00  
% 2.51/1.00  cnf(c_19,negated_conjecture,
% 2.51/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.51/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1555,plain,
% 2.51/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_9,plain,
% 2.51/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.51/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.51/1.00      | ~ v2_pre_topc(X0)
% 2.51/1.00      | ~ l1_pre_topc(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_21,negated_conjecture,
% 2.51/1.00      ( v2_pre_topc(sK0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_302,plain,
% 2.51/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.51/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.51/1.00      | ~ l1_pre_topc(X0)
% 2.51/1.00      | sK0 != X0 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_303,plain,
% 2.51/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | ~ l1_pre_topc(sK0) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_302]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_20,negated_conjecture,
% 2.51/1.00      ( l1_pre_topc(sK0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_307,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_303,c_20]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_308,plain,
% 2.51/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.51/1.00      inference(renaming,[status(thm)],[c_307]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1553,plain,
% 2.51/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
% 2.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2455,plain,
% 2.51/1.00      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1555,c_1553]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_7,plain,
% 2.51/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.51/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1562,plain,
% 2.51/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.51/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_18,negated_conjecture,
% 2.51/1.00      ( v2_tops_1(sK1,sK0)
% 2.51/1.00      | ~ v3_pre_topc(X0,sK0)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | ~ r1_tarski(X0,sK1)
% 2.51/1.00      | k1_xboole_0 = X0 ),
% 2.51/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1556,plain,
% 2.51/1.00      ( k1_xboole_0 = X0
% 2.51/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.51/1.00      | v3_pre_topc(X0,sK0) != iProver_top
% 2.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.51/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2180,plain,
% 2.51/1.00      ( k1_xboole_0 = X0
% 2.51/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.51/1.00      | v3_pre_topc(X0,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.51/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1562,c_1556]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_24,plain,
% 2.51/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_8,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.51/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1762,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1882,plain,
% 2.51/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_1762]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1883,plain,
% 2.51/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.51/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1882]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5,plain,
% 2.51/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.51/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1783,plain,
% 2.51/1.00      ( ~ r1_tarski(X0,X1)
% 2.51/1.00      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 2.51/1.00      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2134,plain,
% 2.51/1.00      ( r1_tarski(X0,u1_struct_0(sK0))
% 2.51/1.00      | ~ r1_tarski(X0,sK1)
% 2.51/1.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_1783]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2135,plain,
% 2.51/1.00      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 2.51/1.00      | r1_tarski(X0,sK1) != iProver_top
% 2.51/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2134]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3871,plain,
% 2.51/1.00      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.51/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.51/1.00      | k1_xboole_0 = X0
% 2.51/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_2180,c_24,c_1883,c_2135]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3872,plain,
% 2.51/1.00      ( k1_xboole_0 = X0
% 2.51/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.51/1.00      | v3_pre_topc(X0,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.51/1.00      inference(renaming,[status(thm)],[c_3871]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3881,plain,
% 2.51/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.51/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.51/1.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_2455,c_3872]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_12,plain,
% 2.51/1.00      ( v2_tops_1(X0,X1)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.00      | ~ l1_pre_topc(X1)
% 2.51/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.51/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_338,plain,
% 2.51/1.00      ( v2_tops_1(X0,X1)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.51/1.00      | sK0 != X1 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_339,plain,
% 2.51/1.00      ( v2_tops_1(X0,sK0)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1696,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0)
% 2.51/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_339]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1697,plain,
% 2.51/1.00      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.51/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 2.51/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1696]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_10,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.51/1.00      | ~ l1_pre_topc(X1) ),
% 2.51/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_374,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.51/1.00      | sK0 != X1 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_375,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_374]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1699,plain,
% 2.51/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_375]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1700,plain,
% 2.51/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.51/1.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_7398,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_3881,c_24,c_1697,c_1700]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_13,plain,
% 2.51/1.00      ( ~ v2_tops_1(X0,X1)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.00      | ~ l1_pre_topc(X1)
% 2.51/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.51/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_323,plain,
% 2.51/1.00      ( ~ v2_tops_1(X0,X1)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.51/1.00      | sK0 != X1 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_324,plain,
% 2.51/1.00      ( ~ v2_tops_1(X0,sK0)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1552,plain,
% 2.51/1.00      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.51/1.00      | v2_tops_1(X0,sK0) != iProver_top
% 2.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2638,plain,
% 2.51/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.51/1.00      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1555,c_1552]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_7403,plain,
% 2.51/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_7398,c_2638]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3,plain,
% 2.51/1.00      ( r1_tarski(X0,X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1565,plain,
% 2.51/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_17,negated_conjecture,
% 2.51/1.00      ( ~ v2_tops_1(sK1,sK0)
% 2.51/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.51/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1557,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_11,plain,
% 2.51/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.00      | ~ r1_tarski(X0,X2)
% 2.51/1.00      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.51/1.00      | ~ l1_pre_topc(X1) ),
% 2.51/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_353,plain,
% 2.51/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.00      | ~ r1_tarski(X0,X2)
% 2.51/1.00      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.51/1.00      | sK0 != X1 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_354,plain,
% 2.51/1.00      ( ~ v3_pre_topc(X0,sK0)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | ~ r1_tarski(X0,X1)
% 2.51/1.00      | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_353]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1550,plain,
% 2.51/1.00      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.51/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.51/1.00      | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1938,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | v3_pre_topc(sK2,sK0) != iProver_top
% 2.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,X0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1557,c_1550]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_28,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_15,negated_conjecture,
% 2.51/1.00      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_403,plain,
% 2.51/1.00      ( ~ v2_tops_1(sK1,sK0)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | ~ r1_tarski(X0,X1)
% 2.51/1.00      | r1_tarski(X0,k1_tops_1(sK0,X1))
% 2.51/1.00      | sK0 != sK0
% 2.51/1.00      | sK2 != X0 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_354]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_404,plain,
% 2.51/1.00      ( ~ v2_tops_1(sK1,sK0)
% 2.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | ~ r1_tarski(sK2,X0)
% 2.51/1.00      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_403]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_405,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.51/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,X0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3395,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,X0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_1938,c_28,c_405]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3405,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.51/1.00      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1555,c_3395]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_16,negated_conjecture,
% 2.51/1.00      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 2.51/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_29,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,sK1) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3567,plain,
% 2.51/1.00      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.51/1.00      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_3405,c_29]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3568,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 2.51/1.00      inference(renaming,[status(thm)],[c_3567]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1563,plain,
% 2.51/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.51/1.00      | r1_tarski(X1,X2) != iProver_top
% 2.51/1.00      | r1_tarski(X0,X2) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3573,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_3568,c_1563]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5783,plain,
% 2.51/1.00      ( r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_3573,c_24,c_1697,c_1700,c_3881]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5791,plain,
% 2.51/1.00      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1565,c_5783]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_7569,plain,
% 2.51/1.00      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.51/1.00      inference(demodulation,[status(thm)],[c_7403,c_5791]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1549,plain,
% 2.51/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.51/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1846,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1557,c_1549]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1,plain,
% 2.51/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.51/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1566,plain,
% 2.51/1.00      ( X0 = X1
% 2.51/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.51/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2857,plain,
% 2.51/1.00      ( k1_tops_1(sK0,sK2) = sK2
% 2.51/1.00      | v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1846,c_1566]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3404,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top
% 2.51/1.00      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1557,c_3395]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3538,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top ),
% 2.51/1.00      inference(forward_subsumption_resolution,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_3404,c_1565]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3541,plain,
% 2.51/1.00      ( k1_tops_1(sK0,sK2) = sK2
% 2.51/1.00      | v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_3538,c_1566]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5430,plain,
% 2.51/1.00      ( k1_tops_1(sK0,sK2) = sK2 ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_2857,c_24,c_1697,c_1700,c_1846,c_3541,c_3881]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2637,plain,
% 2.51/1.00      ( k1_tops_1(sK0,sK2) = k1_xboole_0
% 2.51/1.00      | v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | v2_tops_1(sK2,sK0) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1557,c_1552]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5437,plain,
% 2.51/1.00      ( sK2 = k1_xboole_0
% 2.51/1.00      | v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | v2_tops_1(sK2,sK0) != iProver_top ),
% 2.51/1.00      inference(demodulation,[status(thm)],[c_5430,c_2637]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_14,negated_conjecture,
% 2.51/1.00      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 2.51/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_635,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.51/1.00      | sK0 != sK0
% 2.51/1.00      | sK1 != X0
% 2.51/1.00      | sK2 != k1_xboole_0 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_339]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_636,plain,
% 2.51/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.51/1.00      | sK2 != k1_xboole_0 ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_635]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_638,plain,
% 2.51/1.00      ( k1_tops_1(sK0,sK1) != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_636,c_19]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5468,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | v2_tops_1(sK2,sK0) != iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_5437,c_19,c_24,c_636,c_1697,c_1700,c_2638,c_3881]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5472,plain,
% 2.51/1.00      ( v2_tops_1(sK2,sK0) != iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_5468,c_19,c_24,c_636,c_1697,c_1700,c_2638,c_3881,
% 2.51/1.00                 c_5437]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1551,plain,
% 2.51/1.00      ( k1_tops_1(sK0,X0) != k1_xboole_0
% 2.51/1.00      | v2_tops_1(X0,sK0) = iProver_top
% 2.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5452,plain,
% 2.51/1.00      ( sK2 != k1_xboole_0
% 2.51/1.00      | v2_tops_1(sK2,sK0) = iProver_top
% 2.51/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_5430,c_1551]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1707,plain,
% 2.51/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5338,plain,
% 2.51/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.51/1.00      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_1707]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5339,plain,
% 2.51/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.51/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_5338]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1561,plain,
% 2.51/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.51/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2092,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1557,c_1561]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2895,plain,
% 2.51/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.51/1.00      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_2092,c_1563]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5301,plain,
% 2.51/1.00      ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 2.51/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_2895,c_24,c_1697,c_1700,c_3881]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5309,plain,
% 2.51/1.00      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1565,c_5301]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_0,plain,
% 2.51/1.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.51/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6,plain,
% 2.51/1.00      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 2.51/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_287,plain,
% 2.51/1.00      ( ~ r1_tarski(X0,X1)
% 2.51/1.00      | X0 != X2
% 2.51/1.00      | k4_xboole_0(X3,X1) != X4
% 2.51/1.00      | k3_xboole_0(X2,X4) = k1_xboole_0 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_288,plain,
% 2.51/1.00      ( ~ r1_tarski(X0,X1)
% 2.51/1.00      | k3_xboole_0(X0,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_287]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1554,plain,
% 2.51/1.00      ( k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k1_xboole_0
% 2.51/1.00      | r1_tarski(X0,X2) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2665,plain,
% 2.51/1.00      ( k3_xboole_0(sK2,k4_xboole_0(X0,u1_struct_0(sK0))) = k1_xboole_0
% 2.51/1.00      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_2092,c_1554]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5055,plain,
% 2.51/1.00      ( k3_xboole_0(sK2,k4_xboole_0(X0,u1_struct_0(sK0))) = k1_xboole_0 ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_2665,c_24,c_1697,c_1700,c_3881]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4,plain,
% 2.51/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1564,plain,
% 2.51/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2853,plain,
% 2.51/1.00      ( k3_xboole_0(X0,X1) = X0
% 2.51/1.00      | r1_tarski(X0,k3_xboole_0(X0,X1)) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1564,c_1566]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5059,plain,
% 2.51/1.00      ( k3_xboole_0(sK2,k4_xboole_0(X0,u1_struct_0(sK0))) = sK2
% 2.51/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_5055,c_2853]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5065,plain,
% 2.51/1.00      ( sK2 = k1_xboole_0 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 2.51/1.00      inference(light_normalisation,[status(thm)],[c_5059,c_5055]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(contradiction,plain,
% 2.51/1.00      ( $false ),
% 2.51/1.00      inference(minisat,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_7569,c_5472,c_5452,c_5339,c_5309,c_5065]) ).
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.51/1.00  
% 2.51/1.00  ------                               Statistics
% 2.51/1.00  
% 2.51/1.00  ------ General
% 2.51/1.00  
% 2.51/1.00  abstr_ref_over_cycles:                  0
% 2.51/1.00  abstr_ref_under_cycles:                 0
% 2.51/1.00  gc_basic_clause_elim:                   0
% 2.51/1.00  forced_gc_time:                         0
% 2.51/1.00  parsing_time:                           0.011
% 2.51/1.00  unif_index_cands_time:                  0.
% 2.51/1.00  unif_index_add_time:                    0.
% 2.51/1.00  orderings_time:                         0.
% 2.51/1.00  out_proof_time:                         0.013
% 2.51/1.00  total_time:                             0.218
% 2.51/1.00  num_of_symbols:                         47
% 2.51/1.00  num_of_terms:                           5254
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing
% 2.51/1.00  
% 2.51/1.00  num_of_splits:                          0
% 2.51/1.00  num_of_split_atoms:                     0
% 2.51/1.00  num_of_reused_defs:                     0
% 2.51/1.00  num_eq_ax_congr_red:                    15
% 2.51/1.00  num_of_sem_filtered_clauses:            1
% 2.51/1.00  num_of_subtypes:                        0
% 2.51/1.00  monotx_restored_types:                  0
% 2.51/1.00  sat_num_of_epr_types:                   0
% 2.51/1.00  sat_num_of_non_cyclic_types:            0
% 2.51/1.00  sat_guarded_non_collapsed_types:        0
% 2.51/1.00  num_pure_diseq_elim:                    0
% 2.51/1.00  simp_replaced_by:                       0
% 2.51/1.00  res_preprocessed:                       96
% 2.51/1.00  prep_upred:                             0
% 2.51/1.00  prep_unflattend:                        25
% 2.51/1.00  smt_new_axioms:                         0
% 2.51/1.00  pred_elim_cands:                        4
% 2.51/1.00  pred_elim:                              3
% 2.51/1.00  pred_elim_cl:                           3
% 2.51/1.00  pred_elim_cycles:                       7
% 2.51/1.00  merged_defs:                            8
% 2.51/1.00  merged_defs_ncl:                        0
% 2.51/1.00  bin_hyper_res:                          8
% 2.51/1.00  prep_cycles:                            4
% 2.51/1.00  pred_elim_time:                         0.011
% 2.51/1.00  splitting_time:                         0.
% 2.51/1.00  sem_filter_time:                        0.
% 2.51/1.00  monotx_time:                            0.001
% 2.51/1.00  subtype_inf_time:                       0.
% 2.51/1.00  
% 2.51/1.00  ------ Problem properties
% 2.51/1.00  
% 2.51/1.00  clauses:                                18
% 2.51/1.00  conjectures:                            6
% 2.51/1.00  epr:                                    6
% 2.51/1.00  horn:                                   17
% 2.51/1.00  ground:                                 5
% 2.51/1.00  unary:                                  3
% 2.51/1.00  binary:                                 9
% 2.51/1.00  lits:                                   43
% 2.51/1.00  lits_eq:                                6
% 2.51/1.00  fd_pure:                                0
% 2.51/1.00  fd_pseudo:                              0
% 2.51/1.00  fd_cond:                                1
% 2.51/1.00  fd_pseudo_cond:                         1
% 2.51/1.00  ac_symbols:                             0
% 2.51/1.00  
% 2.51/1.00  ------ Propositional Solver
% 2.51/1.00  
% 2.51/1.00  prop_solver_calls:                      28
% 2.51/1.00  prop_fast_solver_calls:                 972
% 2.51/1.00  smt_solver_calls:                       0
% 2.51/1.00  smt_fast_solver_calls:                  0
% 2.51/1.00  prop_num_of_clauses:                    2813
% 2.51/1.00  prop_preprocess_simplified:             6348
% 2.51/1.00  prop_fo_subsumed:                       51
% 2.51/1.00  prop_solver_time:                       0.
% 2.51/1.00  smt_solver_time:                        0.
% 2.51/1.00  smt_fast_solver_time:                   0.
% 2.51/1.00  prop_fast_solver_time:                  0.
% 2.51/1.00  prop_unsat_core_time:                   0.
% 2.51/1.00  
% 2.51/1.00  ------ QBF
% 2.51/1.00  
% 2.51/1.00  qbf_q_res:                              0
% 2.51/1.00  qbf_num_tautologies:                    0
% 2.51/1.00  qbf_prep_cycles:                        0
% 2.51/1.00  
% 2.51/1.00  ------ BMC1
% 2.51/1.00  
% 2.51/1.00  bmc1_current_bound:                     -1
% 2.51/1.00  bmc1_last_solved_bound:                 -1
% 2.51/1.00  bmc1_unsat_core_size:                   -1
% 2.51/1.00  bmc1_unsat_core_parents_size:           -1
% 2.51/1.00  bmc1_merge_next_fun:                    0
% 2.51/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.51/1.00  
% 2.51/1.00  ------ Instantiation
% 2.51/1.00  
% 2.51/1.00  inst_num_of_clauses:                    782
% 2.51/1.00  inst_num_in_passive:                    117
% 2.51/1.00  inst_num_in_active:                     388
% 2.51/1.00  inst_num_in_unprocessed:                278
% 2.51/1.00  inst_num_of_loops:                      420
% 2.51/1.00  inst_num_of_learning_restarts:          0
% 2.51/1.00  inst_num_moves_active_passive:          27
% 2.51/1.00  inst_lit_activity:                      0
% 2.51/1.00  inst_lit_activity_moves:                0
% 2.51/1.00  inst_num_tautologies:                   0
% 2.51/1.00  inst_num_prop_implied:                  0
% 2.51/1.00  inst_num_existing_simplified:           0
% 2.51/1.00  inst_num_eq_res_simplified:             0
% 2.51/1.00  inst_num_child_elim:                    0
% 2.51/1.00  inst_num_of_dismatching_blockings:      225
% 2.51/1.00  inst_num_of_non_proper_insts:           1156
% 2.51/1.00  inst_num_of_duplicates:                 0
% 2.51/1.00  inst_inst_num_from_inst_to_res:         0
% 2.51/1.00  inst_dismatching_checking_time:         0.
% 2.51/1.00  
% 2.51/1.00  ------ Resolution
% 2.51/1.00  
% 2.51/1.00  res_num_of_clauses:                     0
% 2.51/1.00  res_num_in_passive:                     0
% 2.51/1.00  res_num_in_active:                      0
% 2.51/1.00  res_num_of_loops:                       100
% 2.51/1.00  res_forward_subset_subsumed:            90
% 2.51/1.00  res_backward_subset_subsumed:           4
% 2.51/1.00  res_forward_subsumed:                   0
% 2.51/1.00  res_backward_subsumed:                  0
% 2.51/1.00  res_forward_subsumption_resolution:     0
% 2.51/1.00  res_backward_subsumption_resolution:    0
% 2.51/1.00  res_clause_to_clause_subsumption:       1013
% 2.51/1.00  res_orphan_elimination:                 0
% 2.51/1.00  res_tautology_del:                      143
% 2.51/1.00  res_num_eq_res_simplified:              0
% 2.51/1.00  res_num_sel_changes:                    0
% 2.51/1.00  res_moves_from_active_to_pass:          0
% 2.51/1.00  
% 2.51/1.00  ------ Superposition
% 2.51/1.00  
% 2.51/1.00  sup_time_total:                         0.
% 2.51/1.00  sup_time_generating:                    0.
% 2.51/1.00  sup_time_sim_full:                      0.
% 2.51/1.00  sup_time_sim_immed:                     0.
% 2.51/1.00  
% 2.51/1.00  sup_num_of_clauses:                     111
% 2.51/1.00  sup_num_in_active:                      53
% 2.51/1.00  sup_num_in_passive:                     58
% 2.51/1.00  sup_num_of_loops:                       83
% 2.51/1.00  sup_fw_superposition:                   137
% 2.51/1.00  sup_bw_superposition:                   101
% 2.51/1.00  sup_immediate_simplified:               62
% 2.51/1.00  sup_given_eliminated:                   0
% 2.51/1.00  comparisons_done:                       0
% 2.51/1.00  comparisons_avoided:                    0
% 2.51/1.00  
% 2.51/1.00  ------ Simplifications
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  sim_fw_subset_subsumed:                 20
% 2.51/1.00  sim_bw_subset_subsumed:                 8
% 2.51/1.00  sim_fw_subsumed:                        40
% 2.51/1.00  sim_bw_subsumed:                        3
% 2.51/1.00  sim_fw_subsumption_res:                 3
% 2.51/1.00  sim_bw_subsumption_res:                 0
% 2.51/1.00  sim_tautology_del:                      14
% 2.51/1.00  sim_eq_tautology_del:                   8
% 2.51/1.00  sim_eq_res_simp:                        0
% 2.51/1.00  sim_fw_demodulated:                     4
% 2.51/1.00  sim_bw_demodulated:                     29
% 2.51/1.00  sim_light_normalised:                   16
% 2.51/1.00  sim_joinable_taut:                      0
% 2.51/1.00  sim_joinable_simp:                      0
% 2.51/1.00  sim_ac_normalised:                      0
% 2.51/1.00  sim_smt_subsumption:                    0
% 2.51/1.00  
%------------------------------------------------------------------------------
