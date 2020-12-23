%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:07 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 739 expanded)
%              Number of clauses        :   88 ( 210 expanded)
%              Number of leaves         :   15 ( 177 expanded)
%              Depth                    :   22
%              Number of atoms          :  517 (6004 expanded)
%              Number of equality atoms :  161 (1074 expanded)
%              Maximal formula depth    :   13 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

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

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1496,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1497,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1686,plain,
    ( sK1 = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_1497])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_264,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_265,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_265,c_19])).

cnf(c_270,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_1632,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_1633,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1632])).

cnf(c_11,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_300,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_301,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_1635,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_1636,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_1638,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_1639,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1638])).

cnf(c_1669,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1670,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1669])).

cnf(c_1056,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1776,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1701,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1825,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_1826,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1825])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1712,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2042,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1712])).

cnf(c_2296,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2042])).

cnf(c_2297,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2296])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1646,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2933,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1646])).

cnf(c_2934,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2933])).

cnf(c_1057,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1699,plain,
    ( k1_tops_1(sK0,sK1) != X0
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_3341,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_3422,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1686,c_23,c_1633,c_1636,c_1639,c_1670,c_1776,c_1826,c_2297,c_2934,c_3341])).

cnf(c_12,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_285,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_286,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_1494,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_2446,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_1494])).

cnf(c_3428,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3422,c_2446])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1498,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_315,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_316,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_1492,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1870,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_1492])).

cnf(c_27,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_365,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1))
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_316])).

cnf(c_366,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_367,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_3150,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1870,c_27,c_367])).

cnf(c_3160,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_3150])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3279,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3160,c_28])).

cnf(c_3280,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3279])).

cnf(c_3649,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3428,c_3280])).

cnf(c_4403,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3649,c_23,c_1633,c_1636,c_1639,c_1670,c_1776,c_1826,c_2297,c_2934,c_3341])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1506,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1505,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2603,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1505])).

cnf(c_2620,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_2603])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1507,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2809,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2620,c_1507])).

cnf(c_4410,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4403,c_2809])).

cnf(c_13,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_597,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_301])).

cnf(c_598,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_600,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4410,c_3422,c_2446,c_600])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:30:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.45/0.91  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/0.91  
% 2.45/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/0.91  
% 2.45/0.91  ------  iProver source info
% 2.45/0.91  
% 2.45/0.91  git: date: 2020-06-30 10:37:57 +0100
% 2.45/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/0.91  git: non_committed_changes: false
% 2.45/0.91  git: last_make_outside_of_git: false
% 2.45/0.91  
% 2.45/0.91  ------ 
% 2.45/0.91  
% 2.45/0.91  ------ Input Options
% 2.45/0.91  
% 2.45/0.91  --out_options                           all
% 2.45/0.91  --tptp_safe_out                         true
% 2.45/0.91  --problem_path                          ""
% 2.45/0.91  --include_path                          ""
% 2.45/0.91  --clausifier                            res/vclausify_rel
% 2.45/0.91  --clausifier_options                    --mode clausify
% 2.45/0.91  --stdin                                 false
% 2.45/0.91  --stats_out                             all
% 2.45/0.91  
% 2.45/0.91  ------ General Options
% 2.45/0.91  
% 2.45/0.91  --fof                                   false
% 2.45/0.91  --time_out_real                         305.
% 2.45/0.91  --time_out_virtual                      -1.
% 2.45/0.91  --symbol_type_check                     false
% 2.45/0.91  --clausify_out                          false
% 2.45/0.91  --sig_cnt_out                           false
% 2.45/0.91  --trig_cnt_out                          false
% 2.45/0.91  --trig_cnt_out_tolerance                1.
% 2.45/0.91  --trig_cnt_out_sk_spl                   false
% 2.45/0.91  --abstr_cl_out                          false
% 2.45/0.91  
% 2.45/0.91  ------ Global Options
% 2.45/0.91  
% 2.45/0.91  --schedule                              default
% 2.45/0.91  --add_important_lit                     false
% 2.45/0.91  --prop_solver_per_cl                    1000
% 2.45/0.91  --min_unsat_core                        false
% 2.45/0.91  --soft_assumptions                      false
% 2.45/0.91  --soft_lemma_size                       3
% 2.45/0.91  --prop_impl_unit_size                   0
% 2.45/0.91  --prop_impl_unit                        []
% 2.45/0.91  --share_sel_clauses                     true
% 2.45/0.91  --reset_solvers                         false
% 2.45/0.91  --bc_imp_inh                            [conj_cone]
% 2.45/0.91  --conj_cone_tolerance                   3.
% 2.45/0.91  --extra_neg_conj                        none
% 2.45/0.91  --large_theory_mode                     true
% 2.45/0.91  --prolific_symb_bound                   200
% 2.45/0.91  --lt_threshold                          2000
% 2.45/0.91  --clause_weak_htbl                      true
% 2.45/0.91  --gc_record_bc_elim                     false
% 2.45/0.91  
% 2.45/0.91  ------ Preprocessing Options
% 2.45/0.91  
% 2.45/0.91  --preprocessing_flag                    true
% 2.45/0.91  --time_out_prep_mult                    0.1
% 2.45/0.91  --splitting_mode                        input
% 2.45/0.91  --splitting_grd                         true
% 2.45/0.91  --splitting_cvd                         false
% 2.45/0.91  --splitting_cvd_svl                     false
% 2.45/0.91  --splitting_nvd                         32
% 2.45/0.91  --sub_typing                            true
% 2.45/0.91  --prep_gs_sim                           true
% 2.45/0.91  --prep_unflatten                        true
% 2.45/0.91  --prep_res_sim                          true
% 2.45/0.91  --prep_upred                            true
% 2.45/0.91  --prep_sem_filter                       exhaustive
% 2.45/0.91  --prep_sem_filter_out                   false
% 2.45/0.91  --pred_elim                             true
% 2.45/0.91  --res_sim_input                         true
% 2.45/0.91  --eq_ax_congr_red                       true
% 2.45/0.91  --pure_diseq_elim                       true
% 2.45/0.91  --brand_transform                       false
% 2.45/0.91  --non_eq_to_eq                          false
% 2.45/0.91  --prep_def_merge                        true
% 2.45/0.91  --prep_def_merge_prop_impl              false
% 2.45/0.91  --prep_def_merge_mbd                    true
% 2.45/0.91  --prep_def_merge_tr_red                 false
% 2.45/0.91  --prep_def_merge_tr_cl                  false
% 2.45/0.91  --smt_preprocessing                     true
% 2.45/0.91  --smt_ac_axioms                         fast
% 2.45/0.91  --preprocessed_out                      false
% 2.45/0.91  --preprocessed_stats                    false
% 2.45/0.91  
% 2.45/0.91  ------ Abstraction refinement Options
% 2.45/0.91  
% 2.45/0.91  --abstr_ref                             []
% 2.45/0.91  --abstr_ref_prep                        false
% 2.45/0.91  --abstr_ref_until_sat                   false
% 2.45/0.91  --abstr_ref_sig_restrict                funpre
% 2.45/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/0.91  --abstr_ref_under                       []
% 2.45/0.91  
% 2.45/0.91  ------ SAT Options
% 2.45/0.91  
% 2.45/0.91  --sat_mode                              false
% 2.45/0.91  --sat_fm_restart_options                ""
% 2.45/0.91  --sat_gr_def                            false
% 2.45/0.91  --sat_epr_types                         true
% 2.45/0.91  --sat_non_cyclic_types                  false
% 2.45/0.91  --sat_finite_models                     false
% 2.45/0.91  --sat_fm_lemmas                         false
% 2.45/0.91  --sat_fm_prep                           false
% 2.45/0.91  --sat_fm_uc_incr                        true
% 2.45/0.91  --sat_out_model                         small
% 2.45/0.91  --sat_out_clauses                       false
% 2.45/0.91  
% 2.45/0.91  ------ QBF Options
% 2.45/0.91  
% 2.45/0.91  --qbf_mode                              false
% 2.45/0.91  --qbf_elim_univ                         false
% 2.45/0.91  --qbf_dom_inst                          none
% 2.45/0.91  --qbf_dom_pre_inst                      false
% 2.45/0.91  --qbf_sk_in                             false
% 2.45/0.91  --qbf_pred_elim                         true
% 2.45/0.91  --qbf_split                             512
% 2.45/0.91  
% 2.45/0.91  ------ BMC1 Options
% 2.45/0.91  
% 2.45/0.91  --bmc1_incremental                      false
% 2.45/0.91  --bmc1_axioms                           reachable_all
% 2.45/0.91  --bmc1_min_bound                        0
% 2.45/0.91  --bmc1_max_bound                        -1
% 2.45/0.91  --bmc1_max_bound_default                -1
% 2.45/0.91  --bmc1_symbol_reachability              true
% 2.45/0.91  --bmc1_property_lemmas                  false
% 2.45/0.91  --bmc1_k_induction                      false
% 2.45/0.91  --bmc1_non_equiv_states                 false
% 2.45/0.91  --bmc1_deadlock                         false
% 2.45/0.91  --bmc1_ucm                              false
% 2.45/0.91  --bmc1_add_unsat_core                   none
% 2.45/0.91  --bmc1_unsat_core_children              false
% 2.45/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/0.91  --bmc1_out_stat                         full
% 2.45/0.91  --bmc1_ground_init                      false
% 2.45/0.91  --bmc1_pre_inst_next_state              false
% 2.45/0.91  --bmc1_pre_inst_state                   false
% 2.45/0.91  --bmc1_pre_inst_reach_state             false
% 2.45/0.91  --bmc1_out_unsat_core                   false
% 2.45/0.91  --bmc1_aig_witness_out                  false
% 2.45/0.91  --bmc1_verbose                          false
% 2.45/0.91  --bmc1_dump_clauses_tptp                false
% 2.45/0.91  --bmc1_dump_unsat_core_tptp             false
% 2.45/0.91  --bmc1_dump_file                        -
% 2.45/0.91  --bmc1_ucm_expand_uc_limit              128
% 2.45/0.91  --bmc1_ucm_n_expand_iterations          6
% 2.45/0.91  --bmc1_ucm_extend_mode                  1
% 2.45/0.91  --bmc1_ucm_init_mode                    2
% 2.45/0.91  --bmc1_ucm_cone_mode                    none
% 2.45/0.91  --bmc1_ucm_reduced_relation_type        0
% 2.45/0.91  --bmc1_ucm_relax_model                  4
% 2.45/0.91  --bmc1_ucm_full_tr_after_sat            true
% 2.45/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/0.91  --bmc1_ucm_layered_model                none
% 2.45/0.91  --bmc1_ucm_max_lemma_size               10
% 2.45/0.91  
% 2.45/0.91  ------ AIG Options
% 2.45/0.91  
% 2.45/0.91  --aig_mode                              false
% 2.45/0.91  
% 2.45/0.91  ------ Instantiation Options
% 2.45/0.91  
% 2.45/0.91  --instantiation_flag                    true
% 2.45/0.91  --inst_sos_flag                         false
% 2.45/0.91  --inst_sos_phase                        true
% 2.45/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/0.91  --inst_lit_sel_side                     num_symb
% 2.45/0.91  --inst_solver_per_active                1400
% 2.45/0.91  --inst_solver_calls_frac                1.
% 2.45/0.91  --inst_passive_queue_type               priority_queues
% 2.45/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/0.91  --inst_passive_queues_freq              [25;2]
% 2.45/0.91  --inst_dismatching                      true
% 2.45/0.91  --inst_eager_unprocessed_to_passive     true
% 2.45/0.91  --inst_prop_sim_given                   true
% 2.45/0.91  --inst_prop_sim_new                     false
% 2.45/0.91  --inst_subs_new                         false
% 2.45/0.91  --inst_eq_res_simp                      false
% 2.45/0.91  --inst_subs_given                       false
% 2.45/0.91  --inst_orphan_elimination               true
% 2.45/0.91  --inst_learning_loop_flag               true
% 2.45/0.91  --inst_learning_start                   3000
% 2.45/0.91  --inst_learning_factor                  2
% 2.45/0.91  --inst_start_prop_sim_after_learn       3
% 2.45/0.91  --inst_sel_renew                        solver
% 2.45/0.91  --inst_lit_activity_flag                true
% 2.45/0.91  --inst_restr_to_given                   false
% 2.45/0.91  --inst_activity_threshold               500
% 2.45/0.91  --inst_out_proof                        true
% 2.45/0.91  
% 2.45/0.91  ------ Resolution Options
% 2.45/0.91  
% 2.45/0.91  --resolution_flag                       true
% 2.45/0.91  --res_lit_sel                           adaptive
% 2.45/0.91  --res_lit_sel_side                      none
% 2.45/0.91  --res_ordering                          kbo
% 2.45/0.91  --res_to_prop_solver                    active
% 2.45/0.91  --res_prop_simpl_new                    false
% 2.45/0.91  --res_prop_simpl_given                  true
% 2.45/0.91  --res_passive_queue_type                priority_queues
% 2.45/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/0.91  --res_passive_queues_freq               [15;5]
% 2.45/0.91  --res_forward_subs                      full
% 2.45/0.91  --res_backward_subs                     full
% 2.45/0.91  --res_forward_subs_resolution           true
% 2.45/0.91  --res_backward_subs_resolution          true
% 2.45/0.91  --res_orphan_elimination                true
% 2.45/0.91  --res_time_limit                        2.
% 2.45/0.91  --res_out_proof                         true
% 2.45/0.91  
% 2.45/0.91  ------ Superposition Options
% 2.45/0.91  
% 2.45/0.91  --superposition_flag                    true
% 2.45/0.91  --sup_passive_queue_type                priority_queues
% 2.45/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/0.91  --sup_passive_queues_freq               [8;1;4]
% 2.45/0.91  --demod_completeness_check              fast
% 2.45/0.91  --demod_use_ground                      true
% 2.45/0.91  --sup_to_prop_solver                    passive
% 2.45/0.91  --sup_prop_simpl_new                    true
% 2.45/0.91  --sup_prop_simpl_given                  true
% 2.45/0.91  --sup_fun_splitting                     false
% 2.45/0.91  --sup_smt_interval                      50000
% 2.45/0.91  
% 2.45/0.91  ------ Superposition Simplification Setup
% 2.45/0.91  
% 2.45/0.91  --sup_indices_passive                   []
% 2.45/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.91  --sup_full_bw                           [BwDemod]
% 2.45/0.91  --sup_immed_triv                        [TrivRules]
% 2.45/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.91  --sup_immed_bw_main                     []
% 2.45/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.91  
% 2.45/0.91  ------ Combination Options
% 2.45/0.91  
% 2.45/0.91  --comb_res_mult                         3
% 2.45/0.91  --comb_sup_mult                         2
% 2.45/0.91  --comb_inst_mult                        10
% 2.45/0.91  
% 2.45/0.91  ------ Debug Options
% 2.45/0.91  
% 2.45/0.91  --dbg_backtrace                         false
% 2.45/0.91  --dbg_dump_prop_clauses                 false
% 2.45/0.91  --dbg_dump_prop_clauses_file            -
% 2.45/0.91  --dbg_out_stat                          false
% 2.45/0.91  ------ Parsing...
% 2.45/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/0.91  
% 2.45/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.45/0.91  
% 2.45/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/0.91  
% 2.45/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/0.91  ------ Proving...
% 2.45/0.91  ------ Problem Properties 
% 2.45/0.91  
% 2.45/0.91  
% 2.45/0.91  clauses                                 18
% 2.45/0.91  conjectures                             6
% 2.45/0.91  EPR                                     6
% 2.45/0.91  Horn                                    17
% 2.45/0.91  unary                                   3
% 2.45/0.91  binary                                  9
% 2.45/0.91  lits                                    43
% 2.45/0.91  lits eq                                 6
% 2.45/0.91  fd_pure                                 0
% 2.45/0.91  fd_pseudo                               0
% 2.45/0.91  fd_cond                                 1
% 2.45/0.91  fd_pseudo_cond                          1
% 2.45/0.91  AC symbols                              0
% 2.45/0.91  
% 2.45/0.91  ------ Schedule dynamic 5 is on 
% 2.45/0.91  
% 2.45/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/0.91  
% 2.45/0.91  
% 2.45/0.91  ------ 
% 2.45/0.91  Current options:
% 2.45/0.91  ------ 
% 2.45/0.91  
% 2.45/0.91  ------ Input Options
% 2.45/0.91  
% 2.45/0.91  --out_options                           all
% 2.45/0.91  --tptp_safe_out                         true
% 2.45/0.91  --problem_path                          ""
% 2.45/0.91  --include_path                          ""
% 2.45/0.91  --clausifier                            res/vclausify_rel
% 2.45/0.91  --clausifier_options                    --mode clausify
% 2.45/0.91  --stdin                                 false
% 2.45/0.91  --stats_out                             all
% 2.45/0.91  
% 2.45/0.91  ------ General Options
% 2.45/0.91  
% 2.45/0.91  --fof                                   false
% 2.45/0.91  --time_out_real                         305.
% 2.45/0.91  --time_out_virtual                      -1.
% 2.45/0.91  --symbol_type_check                     false
% 2.45/0.91  --clausify_out                          false
% 2.45/0.91  --sig_cnt_out                           false
% 2.45/0.91  --trig_cnt_out                          false
% 2.45/0.91  --trig_cnt_out_tolerance                1.
% 2.45/0.91  --trig_cnt_out_sk_spl                   false
% 2.45/0.91  --abstr_cl_out                          false
% 2.45/0.91  
% 2.45/0.91  ------ Global Options
% 2.45/0.91  
% 2.45/0.91  --schedule                              default
% 2.45/0.91  --add_important_lit                     false
% 2.45/0.91  --prop_solver_per_cl                    1000
% 2.45/0.91  --min_unsat_core                        false
% 2.45/0.91  --soft_assumptions                      false
% 2.45/0.91  --soft_lemma_size                       3
% 2.45/0.91  --prop_impl_unit_size                   0
% 2.45/0.91  --prop_impl_unit                        []
% 2.45/0.91  --share_sel_clauses                     true
% 2.45/0.91  --reset_solvers                         false
% 2.45/0.91  --bc_imp_inh                            [conj_cone]
% 2.45/0.91  --conj_cone_tolerance                   3.
% 2.45/0.91  --extra_neg_conj                        none
% 2.45/0.91  --large_theory_mode                     true
% 2.45/0.91  --prolific_symb_bound                   200
% 2.45/0.91  --lt_threshold                          2000
% 2.45/0.91  --clause_weak_htbl                      true
% 2.45/0.91  --gc_record_bc_elim                     false
% 2.45/0.91  
% 2.45/0.91  ------ Preprocessing Options
% 2.45/0.91  
% 2.45/0.91  --preprocessing_flag                    true
% 2.45/0.91  --time_out_prep_mult                    0.1
% 2.45/0.91  --splitting_mode                        input
% 2.45/0.91  --splitting_grd                         true
% 2.45/0.91  --splitting_cvd                         false
% 2.45/0.91  --splitting_cvd_svl                     false
% 2.45/0.91  --splitting_nvd                         32
% 2.45/0.91  --sub_typing                            true
% 2.45/0.91  --prep_gs_sim                           true
% 2.45/0.91  --prep_unflatten                        true
% 2.45/0.91  --prep_res_sim                          true
% 2.45/0.91  --prep_upred                            true
% 2.45/0.91  --prep_sem_filter                       exhaustive
% 2.45/0.91  --prep_sem_filter_out                   false
% 2.45/0.91  --pred_elim                             true
% 2.45/0.91  --res_sim_input                         true
% 2.45/0.91  --eq_ax_congr_red                       true
% 2.45/0.91  --pure_diseq_elim                       true
% 2.45/0.91  --brand_transform                       false
% 2.45/0.91  --non_eq_to_eq                          false
% 2.45/0.91  --prep_def_merge                        true
% 2.45/0.91  --prep_def_merge_prop_impl              false
% 2.45/0.91  --prep_def_merge_mbd                    true
% 2.45/0.91  --prep_def_merge_tr_red                 false
% 2.45/0.91  --prep_def_merge_tr_cl                  false
% 2.45/0.91  --smt_preprocessing                     true
% 2.45/0.91  --smt_ac_axioms                         fast
% 2.45/0.91  --preprocessed_out                      false
% 2.45/0.91  --preprocessed_stats                    false
% 2.45/0.91  
% 2.45/0.91  ------ Abstraction refinement Options
% 2.45/0.91  
% 2.45/0.91  --abstr_ref                             []
% 2.45/0.91  --abstr_ref_prep                        false
% 2.45/0.91  --abstr_ref_until_sat                   false
% 2.45/0.91  --abstr_ref_sig_restrict                funpre
% 2.45/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/0.91  --abstr_ref_under                       []
% 2.45/0.91  
% 2.45/0.91  ------ SAT Options
% 2.45/0.91  
% 2.45/0.91  --sat_mode                              false
% 2.45/0.91  --sat_fm_restart_options                ""
% 2.45/0.91  --sat_gr_def                            false
% 2.45/0.91  --sat_epr_types                         true
% 2.45/0.91  --sat_non_cyclic_types                  false
% 2.45/0.91  --sat_finite_models                     false
% 2.45/0.91  --sat_fm_lemmas                         false
% 2.45/0.91  --sat_fm_prep                           false
% 2.45/0.91  --sat_fm_uc_incr                        true
% 2.45/0.91  --sat_out_model                         small
% 2.45/0.91  --sat_out_clauses                       false
% 2.45/0.91  
% 2.45/0.91  ------ QBF Options
% 2.45/0.91  
% 2.45/0.91  --qbf_mode                              false
% 2.45/0.91  --qbf_elim_univ                         false
% 2.45/0.91  --qbf_dom_inst                          none
% 2.45/0.91  --qbf_dom_pre_inst                      false
% 2.45/0.91  --qbf_sk_in                             false
% 2.45/0.91  --qbf_pred_elim                         true
% 2.45/0.91  --qbf_split                             512
% 2.45/0.91  
% 2.45/0.91  ------ BMC1 Options
% 2.45/0.91  
% 2.45/0.91  --bmc1_incremental                      false
% 2.45/0.91  --bmc1_axioms                           reachable_all
% 2.45/0.91  --bmc1_min_bound                        0
% 2.45/0.91  --bmc1_max_bound                        -1
% 2.45/0.91  --bmc1_max_bound_default                -1
% 2.45/0.91  --bmc1_symbol_reachability              true
% 2.45/0.91  --bmc1_property_lemmas                  false
% 2.45/0.91  --bmc1_k_induction                      false
% 2.45/0.91  --bmc1_non_equiv_states                 false
% 2.45/0.91  --bmc1_deadlock                         false
% 2.45/0.91  --bmc1_ucm                              false
% 2.45/0.91  --bmc1_add_unsat_core                   none
% 2.45/0.91  --bmc1_unsat_core_children              false
% 2.45/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/0.91  --bmc1_out_stat                         full
% 2.45/0.91  --bmc1_ground_init                      false
% 2.45/0.91  --bmc1_pre_inst_next_state              false
% 2.45/0.91  --bmc1_pre_inst_state                   false
% 2.45/0.91  --bmc1_pre_inst_reach_state             false
% 2.45/0.91  --bmc1_out_unsat_core                   false
% 2.45/0.91  --bmc1_aig_witness_out                  false
% 2.45/0.91  --bmc1_verbose                          false
% 2.45/0.91  --bmc1_dump_clauses_tptp                false
% 2.45/0.91  --bmc1_dump_unsat_core_tptp             false
% 2.45/0.91  --bmc1_dump_file                        -
% 2.45/0.91  --bmc1_ucm_expand_uc_limit              128
% 2.45/0.91  --bmc1_ucm_n_expand_iterations          6
% 2.45/0.91  --bmc1_ucm_extend_mode                  1
% 2.45/0.91  --bmc1_ucm_init_mode                    2
% 2.45/0.91  --bmc1_ucm_cone_mode                    none
% 2.45/0.91  --bmc1_ucm_reduced_relation_type        0
% 2.45/0.91  --bmc1_ucm_relax_model                  4
% 2.45/0.91  --bmc1_ucm_full_tr_after_sat            true
% 2.45/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/0.91  --bmc1_ucm_layered_model                none
% 2.45/0.91  --bmc1_ucm_max_lemma_size               10
% 2.45/0.91  
% 2.45/0.91  ------ AIG Options
% 2.45/0.91  
% 2.45/0.91  --aig_mode                              false
% 2.45/0.91  
% 2.45/0.91  ------ Instantiation Options
% 2.45/0.91  
% 2.45/0.91  --instantiation_flag                    true
% 2.45/0.91  --inst_sos_flag                         false
% 2.45/0.91  --inst_sos_phase                        true
% 2.45/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/0.91  --inst_lit_sel_side                     none
% 2.45/0.91  --inst_solver_per_active                1400
% 2.45/0.91  --inst_solver_calls_frac                1.
% 2.45/0.91  --inst_passive_queue_type               priority_queues
% 2.45/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/0.91  --inst_passive_queues_freq              [25;2]
% 2.45/0.91  --inst_dismatching                      true
% 2.45/0.91  --inst_eager_unprocessed_to_passive     true
% 2.45/0.91  --inst_prop_sim_given                   true
% 2.45/0.91  --inst_prop_sim_new                     false
% 2.45/0.91  --inst_subs_new                         false
% 2.45/0.91  --inst_eq_res_simp                      false
% 2.45/0.91  --inst_subs_given                       false
% 2.45/0.91  --inst_orphan_elimination               true
% 2.45/0.91  --inst_learning_loop_flag               true
% 2.45/0.91  --inst_learning_start                   3000
% 2.45/0.91  --inst_learning_factor                  2
% 2.45/0.91  --inst_start_prop_sim_after_learn       3
% 2.45/0.91  --inst_sel_renew                        solver
% 2.45/0.91  --inst_lit_activity_flag                true
% 2.45/0.91  --inst_restr_to_given                   false
% 2.45/0.91  --inst_activity_threshold               500
% 2.45/0.91  --inst_out_proof                        true
% 2.45/0.91  
% 2.45/0.91  ------ Resolution Options
% 2.45/0.91  
% 2.45/0.91  --resolution_flag                       false
% 2.45/0.91  --res_lit_sel                           adaptive
% 2.45/0.91  --res_lit_sel_side                      none
% 2.45/0.91  --res_ordering                          kbo
% 2.45/0.91  --res_to_prop_solver                    active
% 2.45/0.91  --res_prop_simpl_new                    false
% 2.45/0.91  --res_prop_simpl_given                  true
% 2.45/0.91  --res_passive_queue_type                priority_queues
% 2.45/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/0.91  --res_passive_queues_freq               [15;5]
% 2.45/0.91  --res_forward_subs                      full
% 2.45/0.91  --res_backward_subs                     full
% 2.45/0.91  --res_forward_subs_resolution           true
% 2.45/0.91  --res_backward_subs_resolution          true
% 2.45/0.91  --res_orphan_elimination                true
% 2.45/0.91  --res_time_limit                        2.
% 2.45/0.91  --res_out_proof                         true
% 2.45/0.91  
% 2.45/0.91  ------ Superposition Options
% 2.45/0.91  
% 2.45/0.91  --superposition_flag                    true
% 2.45/0.91  --sup_passive_queue_type                priority_queues
% 2.45/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/0.91  --sup_passive_queues_freq               [8;1;4]
% 2.45/0.91  --demod_completeness_check              fast
% 2.45/0.91  --demod_use_ground                      true
% 2.45/0.91  --sup_to_prop_solver                    passive
% 2.45/0.91  --sup_prop_simpl_new                    true
% 2.45/0.91  --sup_prop_simpl_given                  true
% 2.45/0.91  --sup_fun_splitting                     false
% 2.45/0.91  --sup_smt_interval                      50000
% 2.45/0.91  
% 2.45/0.91  ------ Superposition Simplification Setup
% 2.45/0.91  
% 2.45/0.91  --sup_indices_passive                   []
% 2.45/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.91  --sup_full_bw                           [BwDemod]
% 2.45/0.91  --sup_immed_triv                        [TrivRules]
% 2.45/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.91  --sup_immed_bw_main                     []
% 2.45/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.91  
% 2.45/0.91  ------ Combination Options
% 2.45/0.91  
% 2.45/0.91  --comb_res_mult                         3
% 2.45/0.91  --comb_sup_mult                         2
% 2.45/0.91  --comb_inst_mult                        10
% 2.45/0.91  
% 2.45/0.91  ------ Debug Options
% 2.45/0.91  
% 2.45/0.91  --dbg_backtrace                         false
% 2.45/0.91  --dbg_dump_prop_clauses                 false
% 2.45/0.91  --dbg_dump_prop_clauses_file            -
% 2.45/0.91  --dbg_out_stat                          false
% 2.45/0.91  
% 2.45/0.91  
% 2.45/0.91  
% 2.45/0.91  
% 2.45/0.91  ------ Proving...
% 2.45/0.91  
% 2.45/0.91  
% 2.45/0.91  % SZS status Theorem for theBenchmark.p
% 2.45/0.91  
% 2.45/0.91  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/0.91  
% 2.45/0.91  fof(f10,conjecture,(
% 2.45/0.91    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.45/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.91  
% 2.45/0.91  fof(f11,negated_conjecture,(
% 2.45/0.91    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.45/0.91    inference(negated_conjecture,[],[f10])).
% 2.45/0.91  
% 2.45/0.91  fof(f21,plain,(
% 2.45/0.91    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.45/0.91    inference(ennf_transformation,[],[f11])).
% 2.45/0.91  
% 2.45/0.91  fof(f22,plain,(
% 2.45/0.91    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.45/0.91    inference(flattening,[],[f21])).
% 2.45/0.91  
% 2.45/0.91  fof(f27,plain,(
% 2.45/0.91    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.45/0.91    inference(nnf_transformation,[],[f22])).
% 2.45/0.91  
% 2.45/0.91  fof(f28,plain,(
% 2.45/0.91    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.45/0.91    inference(flattening,[],[f27])).
% 2.45/0.91  
% 2.45/0.91  fof(f29,plain,(
% 2.45/0.91    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.45/0.91    inference(rectify,[],[f28])).
% 2.45/0.91  
% 2.45/0.91  fof(f32,plain,(
% 2.45/0.91    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.45/0.91    introduced(choice_axiom,[])).
% 2.45/0.91  
% 2.45/0.91  fof(f31,plain,(
% 2.45/0.91    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.45/0.91    introduced(choice_axiom,[])).
% 2.45/0.91  
% 2.45/0.91  fof(f30,plain,(
% 2.45/0.91    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.45/0.91    introduced(choice_axiom,[])).
% 2.45/0.91  
% 2.45/0.91  fof(f33,plain,(
% 2.45/0.91    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.45/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).
% 2.45/0.91  
% 2.45/0.91  fof(f49,plain,(
% 2.45/0.91    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.45/0.91    inference(cnf_transformation,[],[f33])).
% 2.45/0.91  
% 2.45/0.91  fof(f50,plain,(
% 2.45/0.91    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 2.45/0.91    inference(cnf_transformation,[],[f33])).
% 2.45/0.91  
% 2.45/0.91  fof(f6,axiom,(
% 2.45/0.91    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.45/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.91  
% 2.45/0.91  fof(f15,plain,(
% 2.45/0.91    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.45/0.91    inference(ennf_transformation,[],[f6])).
% 2.45/0.91  
% 2.45/0.91  fof(f16,plain,(
% 2.45/0.91    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.45/0.91    inference(flattening,[],[f15])).
% 2.45/0.91  
% 2.45/0.91  fof(f42,plain,(
% 2.45/0.91    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.45/0.91    inference(cnf_transformation,[],[f16])).
% 2.45/0.91  
% 2.45/0.91  fof(f47,plain,(
% 2.45/0.91    v2_pre_topc(sK0)),
% 2.45/0.91    inference(cnf_transformation,[],[f33])).
% 2.45/0.91  
% 2.45/0.91  fof(f48,plain,(
% 2.45/0.91    l1_pre_topc(sK0)),
% 2.45/0.91    inference(cnf_transformation,[],[f33])).
% 2.45/0.91  
% 2.45/0.91  fof(f9,axiom,(
% 2.45/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.45/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.91  
% 2.45/0.91  fof(f20,plain,(
% 2.45/0.91    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.91    inference(ennf_transformation,[],[f9])).
% 2.45/0.91  
% 2.45/0.91  fof(f26,plain,(
% 2.45/0.91    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.91    inference(nnf_transformation,[],[f20])).
% 2.45/0.91  
% 2.45/0.91  fof(f46,plain,(
% 2.45/0.91    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/0.91    inference(cnf_transformation,[],[f26])).
% 2.45/0.91  
% 2.45/0.91  fof(f7,axiom,(
% 2.45/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.45/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.91  
% 2.45/0.91  fof(f17,plain,(
% 2.45/0.91    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.91    inference(ennf_transformation,[],[f7])).
% 2.45/0.91  
% 2.45/0.91  fof(f43,plain,(
% 2.45/0.91    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/0.91    inference(cnf_transformation,[],[f17])).
% 2.45/0.91  
% 2.45/0.91  fof(f5,axiom,(
% 2.45/0.91    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.45/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.91  
% 2.45/0.91  fof(f25,plain,(
% 2.45/0.91    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.45/0.91    inference(nnf_transformation,[],[f5])).
% 2.45/0.91  
% 2.45/0.91  fof(f40,plain,(
% 2.45/0.91    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.45/0.91    inference(cnf_transformation,[],[f25])).
% 2.45/0.91  
% 2.45/0.91  fof(f4,axiom,(
% 2.45/0.91    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.45/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.91  
% 2.45/0.91  fof(f13,plain,(
% 2.45/0.91    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.45/0.91    inference(ennf_transformation,[],[f4])).
% 2.45/0.91  
% 2.45/0.91  fof(f14,plain,(
% 2.45/0.91    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.45/0.91    inference(flattening,[],[f13])).
% 2.45/0.91  
% 2.45/0.91  fof(f39,plain,(
% 2.45/0.91    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.45/0.91    inference(cnf_transformation,[],[f14])).
% 2.45/0.91  
% 2.45/0.91  fof(f41,plain,(
% 2.45/0.91    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.45/0.91    inference(cnf_transformation,[],[f25])).
% 2.45/0.91  
% 2.45/0.91  fof(f45,plain,(
% 2.45/0.91    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/0.91    inference(cnf_transformation,[],[f26])).
% 2.45/0.91  
% 2.45/0.91  fof(f51,plain,(
% 2.45/0.91    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 2.45/0.91    inference(cnf_transformation,[],[f33])).
% 2.45/0.91  
% 2.45/0.91  fof(f8,axiom,(
% 2.45/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.45/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.91  
% 2.45/0.91  fof(f18,plain,(
% 2.45/0.91    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.91    inference(ennf_transformation,[],[f8])).
% 2.45/0.91  
% 2.45/0.91  fof(f19,plain,(
% 2.45/0.91    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.91    inference(flattening,[],[f18])).
% 2.45/0.91  
% 2.45/0.91  fof(f44,plain,(
% 2.45/0.91    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/0.91    inference(cnf_transformation,[],[f19])).
% 2.45/0.91  
% 2.45/0.91  fof(f53,plain,(
% 2.45/0.91    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 2.45/0.91    inference(cnf_transformation,[],[f33])).
% 2.45/0.91  
% 2.45/0.91  fof(f52,plain,(
% 2.45/0.91    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.45/0.91    inference(cnf_transformation,[],[f33])).
% 2.45/0.91  
% 2.45/0.91  fof(f1,axiom,(
% 2.45/0.91    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.45/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.91  
% 2.45/0.91  fof(f23,plain,(
% 2.45/0.91    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.45/0.91    inference(nnf_transformation,[],[f1])).
% 2.45/0.91  
% 2.45/0.91  fof(f24,plain,(
% 2.45/0.91    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.45/0.91    inference(flattening,[],[f23])).
% 2.45/0.91  
% 2.45/0.91  fof(f35,plain,(
% 2.45/0.91    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.45/0.91    inference(cnf_transformation,[],[f24])).
% 2.45/0.91  
% 2.45/0.91  fof(f55,plain,(
% 2.45/0.91    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.45/0.91    inference(equality_resolution,[],[f35])).
% 2.45/0.91  
% 2.45/0.91  fof(f3,axiom,(
% 2.45/0.91    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.45/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.91  
% 2.45/0.91  fof(f38,plain,(
% 2.45/0.91    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.45/0.91    inference(cnf_transformation,[],[f3])).
% 2.45/0.91  
% 2.45/0.91  fof(f2,axiom,(
% 2.45/0.91    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.45/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.91  
% 2.45/0.91  fof(f12,plain,(
% 2.45/0.91    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.45/0.91    inference(ennf_transformation,[],[f2])).
% 2.45/0.91  
% 2.45/0.91  fof(f37,plain,(
% 2.45/0.91    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.45/0.91    inference(cnf_transformation,[],[f12])).
% 2.45/0.91  
% 2.45/0.91  fof(f36,plain,(
% 2.45/0.91    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.45/0.91    inference(cnf_transformation,[],[f24])).
% 2.45/0.91  
% 2.45/0.91  fof(f54,plain,(
% 2.45/0.91    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 2.45/0.91    inference(cnf_transformation,[],[f33])).
% 2.45/0.91  
% 2.45/0.91  cnf(c_18,negated_conjecture,
% 2.45/0.91      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.45/0.91      inference(cnf_transformation,[],[f49]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1496,plain,
% 2.45/0.91      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_17,negated_conjecture,
% 2.45/0.91      ( v2_tops_1(sK1,sK0)
% 2.45/0.91      | ~ v3_pre_topc(X0,sK0)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ r1_tarski(X0,sK1)
% 2.45/0.91      | k1_xboole_0 = X0 ),
% 2.45/0.91      inference(cnf_transformation,[],[f50]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1497,plain,
% 2.45/0.91      ( k1_xboole_0 = X0
% 2.45/0.91      | v2_tops_1(sK1,sK0) = iProver_top
% 2.45/0.91      | v3_pre_topc(X0,sK0) != iProver_top
% 2.45/0.91      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.45/0.91      | r1_tarski(X0,sK1) != iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1686,plain,
% 2.45/0.91      ( sK1 = k1_xboole_0
% 2.45/0.91      | v2_tops_1(sK1,sK0) = iProver_top
% 2.45/0.91      | v3_pre_topc(sK1,sK0) != iProver_top
% 2.45/0.91      | r1_tarski(sK1,sK1) != iProver_top ),
% 2.45/0.91      inference(superposition,[status(thm)],[c_1496,c_1497]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_23,plain,
% 2.45/0.91      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_8,plain,
% 2.45/0.91      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.45/0.91      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.45/0.91      | ~ v2_pre_topc(X0)
% 2.45/0.91      | ~ l1_pre_topc(X0) ),
% 2.45/0.91      inference(cnf_transformation,[],[f42]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_20,negated_conjecture,
% 2.45/0.91      ( v2_pre_topc(sK0) ),
% 2.45/0.91      inference(cnf_transformation,[],[f47]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_264,plain,
% 2.45/0.91      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.45/0.91      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.45/0.91      | ~ l1_pre_topc(X0)
% 2.45/0.91      | sK0 != X0 ),
% 2.45/0.91      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_265,plain,
% 2.45/0.91      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ l1_pre_topc(sK0) ),
% 2.45/0.91      inference(unflattening,[status(thm)],[c_264]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_19,negated_conjecture,
% 2.45/0.91      ( l1_pre_topc(sK0) ),
% 2.45/0.91      inference(cnf_transformation,[],[f48]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_269,plain,
% 2.45/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 2.45/0.91      inference(global_propositional_subsumption,
% 2.45/0.91                [status(thm)],
% 2.45/0.91                [c_265,c_19]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_270,plain,
% 2.45/0.91      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.45/0.91      inference(renaming,[status(thm)],[c_269]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1632,plain,
% 2.45/0.91      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 2.45/0.91      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_270]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1633,plain,
% 2.45/0.91      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top
% 2.45/0.91      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_1632]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_11,plain,
% 2.45/0.91      ( v2_tops_1(X0,X1)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.91      | ~ l1_pre_topc(X1)
% 2.45/0.91      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.45/0.91      inference(cnf_transformation,[],[f46]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_300,plain,
% 2.45/0.91      ( v2_tops_1(X0,X1)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.91      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.45/0.91      | sK0 != X1 ),
% 2.45/0.91      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_301,plain,
% 2.45/0.91      ( v2_tops_1(X0,sK0)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.45/0.91      inference(unflattening,[status(thm)],[c_300]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1635,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0)
% 2.45/0.91      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_301]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1636,plain,
% 2.45/0.91      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.45/0.91      | v2_tops_1(sK1,sK0) = iProver_top
% 2.45/0.91      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_9,plain,
% 2.45/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.91      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.45/0.91      | ~ l1_pre_topc(X1) ),
% 2.45/0.91      inference(cnf_transformation,[],[f43]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_336,plain,
% 2.45/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.91      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.45/0.91      | sK0 != X1 ),
% 2.45/0.91      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_337,plain,
% 2.45/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.45/0.91      inference(unflattening,[status(thm)],[c_336]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1638,plain,
% 2.45/0.91      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_337]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1639,plain,
% 2.45/0.91      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.45/0.91      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_1638]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1669,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0)
% 2.45/0.91      | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 2.45/0.91      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 2.45/0.91      | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_17]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1670,plain,
% 2.45/0.91      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 2.45/0.91      | v2_tops_1(sK1,sK0) = iProver_top
% 2.45/0.91      | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) != iProver_top
% 2.45/0.91      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.45/0.91      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_1669]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1056,plain,( X0 = X0 ),theory(equality) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1776,plain,
% 2.45/0.91      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_1056]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_7,plain,
% 2.45/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.45/0.91      inference(cnf_transformation,[],[f40]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1701,plain,
% 2.45/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_7]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1825,plain,
% 2.45/0.91      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_1701]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1826,plain,
% 2.45/0.91      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.45/0.91      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_1825]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_5,plain,
% 2.45/0.91      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.45/0.91      inference(cnf_transformation,[],[f39]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1712,plain,
% 2.45/0.91      ( ~ r1_tarski(X0,X1)
% 2.45/0.91      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 2.45/0.91      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_5]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_2042,plain,
% 2.45/0.91      ( r1_tarski(X0,u1_struct_0(sK0))
% 2.45/0.91      | ~ r1_tarski(X0,sK1)
% 2.45/0.91      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_1712]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_2296,plain,
% 2.45/0.91      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 2.45/0.91      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 2.45/0.91      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_2042]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_2297,plain,
% 2.45/0.91      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 2.45/0.91      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 2.45/0.91      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_2296]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_6,plain,
% 2.45/0.91      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.45/0.91      inference(cnf_transformation,[],[f41]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1646,plain,
% 2.45/0.91      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_6]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_2933,plain,
% 2.45/0.91      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_1646]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_2934,plain,
% 2.45/0.91      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.45/0.91      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_2933]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1057,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1699,plain,
% 2.45/0.91      ( k1_tops_1(sK0,sK1) != X0
% 2.45/0.91      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.45/0.91      | k1_xboole_0 != X0 ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_1057]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_3341,plain,
% 2.45/0.91      ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 2.45/0.91      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.45/0.91      | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 2.45/0.91      inference(instantiation,[status(thm)],[c_1699]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_3422,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 2.45/0.91      inference(global_propositional_subsumption,
% 2.45/0.91                [status(thm)],
% 2.45/0.91                [c_1686,c_23,c_1633,c_1636,c_1639,c_1670,c_1776,c_1826,
% 2.45/0.91                 c_2297,c_2934,c_3341]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_12,plain,
% 2.45/0.91      ( ~ v2_tops_1(X0,X1)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.91      | ~ l1_pre_topc(X1)
% 2.45/0.91      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.45/0.91      inference(cnf_transformation,[],[f45]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_285,plain,
% 2.45/0.91      ( ~ v2_tops_1(X0,X1)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.91      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.45/0.91      | sK0 != X1 ),
% 2.45/0.91      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_286,plain,
% 2.45/0.91      ( ~ v2_tops_1(X0,sK0)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.45/0.91      inference(unflattening,[status(thm)],[c_285]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1494,plain,
% 2.45/0.91      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.45/0.91      | v2_tops_1(X0,sK0) != iProver_top
% 2.45/0.91      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_2446,plain,
% 2.45/0.91      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.45/0.91      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.45/0.91      inference(superposition,[status(thm)],[c_1496,c_1494]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_3428,plain,
% 2.45/0.91      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.45/0.91      inference(superposition,[status(thm)],[c_3422,c_2446]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_16,negated_conjecture,
% 2.45/0.91      ( ~ v2_tops_1(sK1,sK0)
% 2.45/0.91      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.45/0.91      inference(cnf_transformation,[],[f51]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1498,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.45/0.91      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_10,plain,
% 2.45/0.91      ( ~ v3_pre_topc(X0,X1)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.91      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.91      | ~ r1_tarski(X0,X2)
% 2.45/0.91      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.45/0.91      | ~ l1_pre_topc(X1) ),
% 2.45/0.91      inference(cnf_transformation,[],[f44]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_315,plain,
% 2.45/0.91      ( ~ v3_pre_topc(X0,X1)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.91      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.91      | ~ r1_tarski(X0,X2)
% 2.45/0.91      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.45/0.91      | sK0 != X1 ),
% 2.45/0.91      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_316,plain,
% 2.45/0.91      ( ~ v3_pre_topc(X0,sK0)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ r1_tarski(X0,X1)
% 2.45/0.91      | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
% 2.45/0.91      inference(unflattening,[status(thm)],[c_315]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1492,plain,
% 2.45/0.91      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.45/0.91      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.45/0.91      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.45/0.91      | r1_tarski(X0,X1) != iProver_top
% 2.45/0.91      | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1870,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.45/0.91      | v3_pre_topc(sK2,sK0) != iProver_top
% 2.45/0.91      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.45/0.91      | r1_tarski(sK2,X0) != iProver_top
% 2.45/0.91      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.45/0.91      inference(superposition,[status(thm)],[c_1498,c_1492]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_27,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.45/0.91      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_14,negated_conjecture,
% 2.45/0.91      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 2.45/0.91      inference(cnf_transformation,[],[f53]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_365,plain,
% 2.45/0.91      ( ~ v2_tops_1(sK1,sK0)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ r1_tarski(X0,X1)
% 2.45/0.91      | r1_tarski(X0,k1_tops_1(sK0,X1))
% 2.45/0.91      | sK0 != sK0
% 2.45/0.91      | sK2 != X0 ),
% 2.45/0.91      inference(resolution_lifted,[status(thm)],[c_14,c_316]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_366,plain,
% 2.45/0.91      ( ~ v2_tops_1(sK1,sK0)
% 2.45/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | ~ r1_tarski(sK2,X0)
% 2.45/0.91      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.45/0.91      inference(unflattening,[status(thm)],[c_365]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_367,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.45/0.91      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.45/0.91      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.45/0.91      | r1_tarski(sK2,X0) != iProver_top
% 2.45/0.91      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_3150,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.45/0.91      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.45/0.91      | r1_tarski(sK2,X0) != iProver_top
% 2.45/0.91      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.45/0.91      inference(global_propositional_subsumption,
% 2.45/0.91                [status(thm)],
% 2.45/0.91                [c_1870,c_27,c_367]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_3160,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.45/0.91      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.45/0.91      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.45/0.91      inference(superposition,[status(thm)],[c_1496,c_3150]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_15,negated_conjecture,
% 2.45/0.91      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 2.45/0.91      inference(cnf_transformation,[],[f52]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_28,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.45/0.91      | r1_tarski(sK2,sK1) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_3279,plain,
% 2.45/0.91      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.45/0.91      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.45/0.91      inference(global_propositional_subsumption,
% 2.45/0.91                [status(thm)],
% 2.45/0.91                [c_3160,c_28]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_3280,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.45/0.91      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 2.45/0.91      inference(renaming,[status(thm)],[c_3279]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_3649,plain,
% 2.45/0.91      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.45/0.91      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.45/0.91      inference(demodulation,[status(thm)],[c_3428,c_3280]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_4403,plain,
% 2.45/0.91      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.45/0.91      inference(global_propositional_subsumption,
% 2.45/0.91                [status(thm)],
% 2.45/0.91                [c_3649,c_23,c_1633,c_1636,c_1639,c_1670,c_1776,c_1826,
% 2.45/0.91                 c_2297,c_2934,c_3341]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1,plain,
% 2.45/0.91      ( r1_tarski(X0,X0) ),
% 2.45/0.91      inference(cnf_transformation,[],[f55]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1506,plain,
% 2.45/0.91      ( r1_tarski(X0,X0) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_4,plain,
% 2.45/0.91      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.45/0.91      inference(cnf_transformation,[],[f38]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_3,plain,
% 2.45/0.91      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 2.45/0.91      inference(cnf_transformation,[],[f37]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1505,plain,
% 2.45/0.91      ( r1_tarski(X0,X1) != iProver_top
% 2.45/0.91      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_2603,plain,
% 2.45/0.91      ( r1_tarski(X0,X1) = iProver_top
% 2.45/0.91      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.45/0.91      inference(superposition,[status(thm)],[c_4,c_1505]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_2620,plain,
% 2.45/0.91      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.45/0.91      inference(superposition,[status(thm)],[c_1506,c_2603]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_0,plain,
% 2.45/0.91      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.45/0.91      inference(cnf_transformation,[],[f36]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_1507,plain,
% 2.45/0.91      ( X0 = X1
% 2.45/0.91      | r1_tarski(X0,X1) != iProver_top
% 2.45/0.91      | r1_tarski(X1,X0) != iProver_top ),
% 2.45/0.91      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_2809,plain,
% 2.45/0.91      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.45/0.91      inference(superposition,[status(thm)],[c_2620,c_1507]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_4410,plain,
% 2.45/0.91      ( sK2 = k1_xboole_0 ),
% 2.45/0.91      inference(superposition,[status(thm)],[c_4403,c_2809]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_13,negated_conjecture,
% 2.45/0.91      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 2.45/0.91      inference(cnf_transformation,[],[f54]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_597,plain,
% 2.45/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.45/0.91      | sK0 != sK0
% 2.45/0.91      | sK1 != X0
% 2.45/0.91      | sK2 != k1_xboole_0 ),
% 2.45/0.91      inference(resolution_lifted,[status(thm)],[c_13,c_301]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_598,plain,
% 2.45/0.91      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/0.91      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.45/0.91      | sK2 != k1_xboole_0 ),
% 2.45/0.91      inference(unflattening,[status(thm)],[c_597]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(c_600,plain,
% 2.45/0.91      ( k1_tops_1(sK0,sK1) != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.45/0.91      inference(global_propositional_subsumption,
% 2.45/0.91                [status(thm)],
% 2.45/0.91                [c_598,c_18]) ).
% 2.45/0.91  
% 2.45/0.91  cnf(contradiction,plain,
% 2.45/0.91      ( $false ),
% 2.45/0.91      inference(minisat,[status(thm)],[c_4410,c_3422,c_2446,c_600]) ).
% 2.45/0.91  
% 2.45/0.91  
% 2.45/0.91  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/0.91  
% 2.45/0.91  ------                               Statistics
% 2.45/0.91  
% 2.45/0.91  ------ General
% 2.45/0.91  
% 2.45/0.91  abstr_ref_over_cycles:                  0
% 2.45/0.91  abstr_ref_under_cycles:                 0
% 2.45/0.91  gc_basic_clause_elim:                   0
% 2.45/0.91  forced_gc_time:                         0
% 2.45/0.91  parsing_time:                           0.008
% 2.45/0.91  unif_index_cands_time:                  0.
% 2.45/0.91  unif_index_add_time:                    0.
% 2.45/0.91  orderings_time:                         0.
% 2.45/0.91  out_proof_time:                         0.008
% 2.45/0.91  total_time:                             0.14
% 2.45/0.91  num_of_symbols:                         45
% 2.45/0.91  num_of_terms:                           2543
% 2.45/0.91  
% 2.45/0.91  ------ Preprocessing
% 2.45/0.91  
% 2.45/0.91  num_of_splits:                          0
% 2.45/0.91  num_of_split_atoms:                     0
% 2.45/0.91  num_of_reused_defs:                     0
% 2.45/0.91  num_eq_ax_congr_red:                    7
% 2.45/0.91  num_of_sem_filtered_clauses:            1
% 2.45/0.91  num_of_subtypes:                        0
% 2.45/0.91  monotx_restored_types:                  0
% 2.45/0.91  sat_num_of_epr_types:                   0
% 2.45/0.91  sat_num_of_non_cyclic_types:            0
% 2.45/0.91  sat_guarded_non_collapsed_types:        0
% 2.45/0.91  num_pure_diseq_elim:                    0
% 2.45/0.91  simp_replaced_by:                       0
% 2.45/0.91  res_preprocessed:                       95
% 2.45/0.91  prep_upred:                             0
% 2.45/0.91  prep_unflattend:                        23
% 2.45/0.91  smt_new_axioms:                         0
% 2.45/0.91  pred_elim_cands:                        4
% 2.45/0.91  pred_elim:                              2
% 2.45/0.91  pred_elim_cl:                           2
% 2.45/0.91  pred_elim_cycles:                       6
% 2.45/0.91  merged_defs:                            8
% 2.45/0.91  merged_defs_ncl:                        0
% 2.45/0.91  bin_hyper_res:                          8
% 2.45/0.91  prep_cycles:                            4
% 2.45/0.91  pred_elim_time:                         0.011
% 2.45/0.91  splitting_time:                         0.
% 2.45/0.91  sem_filter_time:                        0.
% 2.45/0.91  monotx_time:                            0.
% 2.45/0.91  subtype_inf_time:                       0.
% 2.45/0.91  
% 2.45/0.91  ------ Problem properties
% 2.45/0.91  
% 2.45/0.91  clauses:                                18
% 2.45/0.91  conjectures:                            6
% 2.45/0.91  epr:                                    6
% 2.45/0.91  horn:                                   17
% 2.45/0.91  ground:                                 5
% 2.45/0.91  unary:                                  3
% 2.45/0.91  binary:                                 9
% 2.45/0.91  lits:                                   43
% 2.45/0.91  lits_eq:                                6
% 2.45/0.91  fd_pure:                                0
% 2.45/0.91  fd_pseudo:                              0
% 2.45/0.91  fd_cond:                                1
% 2.45/0.91  fd_pseudo_cond:                         1
% 2.45/0.91  ac_symbols:                             0
% 2.45/0.91  
% 2.45/0.91  ------ Propositional Solver
% 2.45/0.91  
% 2.45/0.91  prop_solver_calls:                      28
% 2.45/0.91  prop_fast_solver_calls:                 780
% 2.45/0.91  smt_solver_calls:                       0
% 2.45/0.91  smt_fast_solver_calls:                  0
% 2.45/0.91  prop_num_of_clauses:                    1353
% 2.45/0.91  prop_preprocess_simplified:             4392
% 2.45/0.91  prop_fo_subsumed:                       24
% 2.45/0.91  prop_solver_time:                       0.
% 2.45/0.91  smt_solver_time:                        0.
% 2.45/0.91  smt_fast_solver_time:                   0.
% 2.45/0.91  prop_fast_solver_time:                  0.
% 2.45/0.91  prop_unsat_core_time:                   0.
% 2.45/0.91  
% 2.45/0.91  ------ QBF
% 2.45/0.91  
% 2.45/0.91  qbf_q_res:                              0
% 2.45/0.91  qbf_num_tautologies:                    0
% 2.45/0.91  qbf_prep_cycles:                        0
% 2.45/0.91  
% 2.45/0.91  ------ BMC1
% 2.45/0.91  
% 2.45/0.91  bmc1_current_bound:                     -1
% 2.45/0.91  bmc1_last_solved_bound:                 -1
% 2.45/0.91  bmc1_unsat_core_size:                   -1
% 2.45/0.91  bmc1_unsat_core_parents_size:           -1
% 2.45/0.91  bmc1_merge_next_fun:                    0
% 2.45/0.91  bmc1_unsat_core_clauses_time:           0.
% 2.45/0.91  
% 2.45/0.91  ------ Instantiation
% 2.45/0.91  
% 2.45/0.91  inst_num_of_clauses:                    447
% 2.45/0.91  inst_num_in_passive:                    17
% 2.45/0.91  inst_num_in_active:                     244
% 2.45/0.91  inst_num_in_unprocessed:                187
% 2.45/0.91  inst_num_of_loops:                      260
% 2.45/0.91  inst_num_of_learning_restarts:          0
% 2.45/0.91  inst_num_moves_active_passive:          12
% 2.45/0.91  inst_lit_activity:                      0
% 2.45/0.91  inst_lit_activity_moves:                0
% 2.45/0.91  inst_num_tautologies:                   0
% 2.45/0.91  inst_num_prop_implied:                  0
% 2.45/0.91  inst_num_existing_simplified:           0
% 2.45/0.91  inst_num_eq_res_simplified:             0
% 2.45/0.91  inst_num_child_elim:                    0
% 2.45/0.91  inst_num_of_dismatching_blockings:      104
% 2.45/0.91  inst_num_of_non_proper_insts:           624
% 2.45/0.91  inst_num_of_duplicates:                 0
% 2.45/0.91  inst_inst_num_from_inst_to_res:         0
% 2.45/0.91  inst_dismatching_checking_time:         0.
% 2.45/0.91  
% 2.45/0.91  ------ Resolution
% 2.45/0.91  
% 2.45/0.91  res_num_of_clauses:                     0
% 2.45/0.91  res_num_in_passive:                     0
% 2.45/0.91  res_num_in_active:                      0
% 2.45/0.91  res_num_of_loops:                       99
% 2.45/0.91  res_forward_subset_subsumed:            57
% 2.45/0.91  res_backward_subset_subsumed:           4
% 2.45/0.91  res_forward_subsumed:                   0
% 2.45/0.91  res_backward_subsumed:                  0
% 2.45/0.91  res_forward_subsumption_resolution:     0
% 2.45/0.91  res_backward_subsumption_resolution:    0
% 2.45/0.91  res_clause_to_clause_subsumption:       541
% 2.45/0.91  res_orphan_elimination:                 0
% 2.45/0.91  res_tautology_del:                      87
% 2.45/0.91  res_num_eq_res_simplified:              0
% 2.45/0.91  res_num_sel_changes:                    0
% 2.45/0.91  res_moves_from_active_to_pass:          0
% 2.45/0.91  
% 2.45/0.91  ------ Superposition
% 2.45/0.91  
% 2.45/0.91  sup_time_total:                         0.
% 2.45/0.91  sup_time_generating:                    0.
% 2.45/0.91  sup_time_sim_full:                      0.
% 2.45/0.91  sup_time_sim_immed:                     0.
% 2.45/0.91  
% 2.45/0.91  sup_num_of_clauses:                     80
% 2.45/0.91  sup_num_in_active:                      46
% 2.45/0.91  sup_num_in_passive:                     34
% 2.45/0.91  sup_num_of_loops:                       51
% 2.45/0.91  sup_fw_superposition:                   46
% 2.45/0.91  sup_bw_superposition:                   34
% 2.45/0.91  sup_immediate_simplified:               7
% 2.45/0.91  sup_given_eliminated:                   1
% 2.45/0.91  comparisons_done:                       0
% 2.45/0.91  comparisons_avoided:                    0
% 2.45/0.91  
% 2.45/0.91  ------ Simplifications
% 2.45/0.91  
% 2.45/0.91  
% 2.45/0.91  sim_fw_subset_subsumed:                 3
% 2.45/0.91  sim_bw_subset_subsumed:                 1
% 2.45/0.91  sim_fw_subsumed:                        4
% 2.45/0.91  sim_bw_subsumed:                        1
% 2.45/0.91  sim_fw_subsumption_res:                 2
% 2.45/0.91  sim_bw_subsumption_res:                 0
% 2.45/0.91  sim_tautology_del:                      3
% 2.45/0.91  sim_eq_tautology_del:                   2
% 2.45/0.91  sim_eq_res_simp:                        0
% 2.45/0.91  sim_fw_demodulated:                     0
% 2.45/0.91  sim_bw_demodulated:                     4
% 2.45/0.91  sim_light_normalised:                   3
% 2.45/0.91  sim_joinable_taut:                      0
% 2.45/0.91  sim_joinable_simp:                      0
% 2.45/0.91  sim_ac_normalised:                      0
% 2.45/0.91  sim_smt_subsumption:                    0
% 2.45/0.91  
%------------------------------------------------------------------------------
