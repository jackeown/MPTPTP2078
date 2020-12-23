%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1268+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:17 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 763 expanded)
%              Number of clauses        :  109 ( 206 expanded)
%              Number of leaves         :   12 ( 180 expanded)
%              Depth                    :   20
%              Number of atoms          :  674 (6681 expanded)
%              Number of equality atoms :  141 (1093 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 != X2
          & v3_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK3
        & v3_pre_topc(sK3,X0)
        & r1_tarski(sK3,X1)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
              & r1_tarski(X2,sK2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tops_1(sK2,X0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,X0)
              | ~ r1_tarski(X3,sK2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v2_tops_1(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
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
                & v3_pre_topc(X2,sK1)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
            | ~ v2_tops_1(X1,sK1) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK1)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            | v2_tops_1(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ( k1_xboole_0 != sK3
        & v3_pre_topc(sK3,sK1)
        & r1_tarski(sK3,sK2)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ v2_tops_1(sK2,sK1) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK1)
          | ~ r1_tarski(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | v2_tops_1(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f27,f26,f25])).

fof(f44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | ? [X2] :
                  ( r1_xboole_0(X1,X2)
                  & v3_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ~ r1_xboole_0(X1,X2)
                  | ~ v3_pre_topc(X2,X0)
                  | k1_xboole_0 = X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | ? [X2] :
                  ( r1_xboole_0(X1,X2)
                  & v3_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( ~ r1_xboole_0(X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r1_xboole_0(X1,X2)
          & v3_pre_topc(X2,X0)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK0(X0,X1))
        & v3_pre_topc(sK0(X0,X1),X0)
        & k1_xboole_0 != sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | ( r1_xboole_0(X1,sK0(X0,X1))
                & v3_pre_topc(sK0(X0,X1),X0)
                & k1_xboole_0 != sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( ~ r1_xboole_0(X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_xboole_0(X1,X3)
      | ~ v3_pre_topc(X3,X0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,
    ( r1_tarski(sK3,sK2)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,
    ( k1_xboole_0 != sK3
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK1)
      | ~ r1_tarski(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_tops_1(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | r1_xboole_0(X1,sK0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k1_xboole_0 != sK0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | v3_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_1727,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_2764,plain,
    ( sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)) = sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)) ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_2765,plain,
    ( sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_2764])).

cnf(c_1728,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_2508,plain,
    ( sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)) != X1_44
    | sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)) = k1_xboole_0
    | k1_xboole_0 != X1_44 ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_2688,plain,
    ( sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)) != sK0(sK1,k3_subset_1(u1_struct_0(sK1),X1_44))
    | sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)) = k1_xboole_0
    | k1_xboole_0 != sK0(sK1,k3_subset_1(u1_struct_0(sK1),X1_44)) ),
    inference(instantiation,[status(thm)],[c_2508])).

cnf(c_2689,plain,
    ( sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) != sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2))
    | sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k1_xboole_0
    | k1_xboole_0 != sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_2688])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1722,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ r1_xboole_0(X0_44,k3_subset_1(X0_46,X1_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_46))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2308,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ r1_xboole_0(X0_44,k3_subset_1(u1_struct_0(sK1),X1_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_2656,plain,
    ( r1_tarski(sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)),X0_44)
    | ~ r1_xboole_0(sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)),k3_subset_1(u1_struct_0(sK1),X0_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2308])).

cnf(c_2658,plain,
    ( r1_tarski(sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)),sK2)
    | ~ r1_xboole_0(sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)),k3_subset_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2656])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1718,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tops_1(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2100,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1718])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1716,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1716])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r1_xboole_0(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_298,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r1_xboole_0(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_299,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ r1_xboole_0(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tops_1(X1,sK1)
    | ~ l1_pre_topc(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_303,plain,
    ( ~ v1_tops_1(X1,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(X1,X0)
    | ~ v3_pre_topc(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_299,c_17])).

cnf(c_304,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ r1_xboole_0(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tops_1(X1,sK1)
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_1715,plain,
    ( ~ v3_pre_topc(X0_44,sK1)
    | ~ r1_xboole_0(X1_44,X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tops_1(X1_44,sK1)
    | k1_xboole_0 = X0_44 ),
    inference(subtyping,[status(esa)],[c_304])).

cnf(c_2103,plain,
    ( k1_xboole_0 = X0_44
    | v3_pre_topc(X0_44,sK1) != iProver_top
    | r1_xboole_0(X1_44,X0_44) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_tops_1(X1_44,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1715])).

cnf(c_2533,plain,
    ( sK2 = k1_xboole_0
    | v3_pre_topc(sK2,sK1) != iProver_top
    | r1_xboole_0(X0_44,sK2) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_tops_1(X0_44,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2102,c_2103])).

cnf(c_2584,plain,
    ( sK2 = k1_xboole_0
    | v3_pre_topc(sK2,sK1) != iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top
    | v1_tops_1(sK3,sK1) != iProver_top
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2533])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK3,sK2)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( r1_tarski(sK3,sK2) = iProver_top
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_27,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1721,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | k1_xboole_0 != sK3 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1753,plain,
    ( k1_xboole_0 != sK3
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1721])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ v2_tops_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ v2_tops_1(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | ~ v2_tops_1(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1710,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0_44),sK1)
    | ~ v2_tops_1(X0_44,sK1) ),
    inference(subtyping,[status(esa)],[c_436])).

cnf(c_1776,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0_44),sK1) = iProver_top
    | v2_tops_1(X0_44,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1710])).

cnf(c_1778,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1776])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1725,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_46))
    | m1_subset_1(k3_subset_1(X0_46,X0_44),k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2275,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_2276,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2275])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1723,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_xboole_0(X0_44,k3_subset_1(X0_46,X1_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_46))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2340,plain,
    ( ~ r1_tarski(sK3,sK2)
    | r1_xboole_0(sK3,k3_subset_1(X0_46,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_46))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_46)) ),
    inference(instantiation,[status(thm)],[c_1723])).

cnf(c_2378,plain,
    ( ~ r1_tarski(sK3,sK2)
    | r1_xboole_0(sK3,k3_subset_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2340])).

cnf(c_2379,plain,
    ( r1_tarski(sK3,sK2) != iProver_top
    | r1_xboole_0(sK3,k3_subset_1(u1_struct_0(sK1),sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2378])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1724,plain,
    ( ~ r1_xboole_0(X0_44,X1_44)
    | r1_xboole_0(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2417,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK1),sK2),sK3)
    | ~ r1_xboole_0(sK3,k3_subset_1(u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_2423,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK1),sK2),sK3) = iProver_top
    | r1_xboole_0(sK3,k3_subset_1(u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2417])).

cnf(c_2350,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ r1_xboole_0(X0_44,sK3)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tops_1(X0_44,sK1)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1715])).

cnf(c_2439,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK1),sK2),sK3)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2350])).

cnf(c_2440,plain,
    ( k1_xboole_0 = sK3
    | v3_pre_topc(sK3,sK1) != iProver_top
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK1),sK2),sK3) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2439])).

cnf(c_2634,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2584,c_21,c_25,c_26,c_27,c_1753,c_1778,c_2276,c_2379,c_2423,c_2440])).

cnf(c_2636,plain,
    ( ~ v2_tops_1(sK2,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2634])).

cnf(c_2513,plain,
    ( r1_xboole_0(sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)),k3_subset_1(u1_struct_0(sK1),X0_44))
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK1),X0_44),sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44))) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_2520,plain,
    ( r1_xboole_0(sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)),k3_subset_1(u1_struct_0(sK1),sK2))
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK1),sK2),sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2))) ),
    inference(instantiation,[status(thm)],[c_2513])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ r1_tarski(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tops_1(sK2,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1717,negated_conjecture,
    ( ~ v3_pre_topc(X0_44,sK1)
    | ~ r1_tarski(X0_44,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tops_1(sK2,sK1)
    | k1_xboole_0 = X0_44 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2494,plain,
    ( ~ v3_pre_topc(sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)),sK1)
    | ~ r1_tarski(sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)),sK2)
    | ~ m1_subset_1(sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tops_1(sK2,sK1)
    | k1_xboole_0 = sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)) ),
    inference(instantiation,[status(thm)],[c_1717])).

cnf(c_2496,plain,
    ( ~ v3_pre_topc(sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)),sK1)
    | ~ r1_tarski(sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)),sK2)
    | ~ m1_subset_1(sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tops_1(sK2,sK1)
    | k1_xboole_0 = sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_2494])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,sK0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_370,plain,
    ( r1_xboole_0(X0,sK0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_371,plain,
    ( r1_xboole_0(X0,sK0(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_375,plain,
    ( v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_xboole_0(X0,sK0(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_371,c_17])).

cnf(c_376,plain,
    ( r1_xboole_0(X0,sK0(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0,sK1) ),
    inference(renaming,[status(thm)],[c_375])).

cnf(c_1712,plain,
    ( r1_xboole_0(X0_44,sK0(sK1,X0_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0_44,sK1) ),
    inference(subtyping,[status(esa)],[c_376])).

cnf(c_2270,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK1),X0_44),sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0_44),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0_44),sK1) ),
    inference(instantiation,[status(thm)],[c_1712])).

cnf(c_2272,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK1),sK2),sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_2270])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_333,plain,
    ( v1_tops_1(X0,sK1)
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_329,c_17])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0,sK1) ),
    inference(renaming,[status(thm)],[c_333])).

cnf(c_1714,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0_44),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0_44,sK1) ),
    inference(subtyping,[status(esa)],[c_334])).

cnf(c_2265,plain,
    ( m1_subset_1(sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0_44),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0_44),sK1) ),
    inference(instantiation,[status(thm)],[c_1714])).

cnf(c_2267,plain,
    ( m1_subset_1(sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_2265])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_354,plain,
    ( v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,X0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_17])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0,sK1)
    | sK0(sK1,X0) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_1713,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0_44,sK1)
    | sK0(sK1,X0_44) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_355])).

cnf(c_2255,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0_44),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0_44),sK1)
    | sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1713])).

cnf(c_2256,plain,
    ( sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)) != k1_xboole_0
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0_44),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0_44),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2255])).

cnf(c_2258,plain,
    ( sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) != k1_xboole_0
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2256])).

cnf(c_7,plain,
    ( v3_pre_topc(sK0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_tops_1(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_391,plain,
    ( v3_pre_topc(sK0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_tops_1(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_392,plain,
    ( v3_pre_topc(sK0(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_396,plain,
    ( v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK0(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_17])).

cnf(c_397,plain,
    ( v3_pre_topc(sK0(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0,sK1) ),
    inference(renaming,[status(thm)],[c_396])).

cnf(c_1711,plain,
    ( v3_pre_topc(sK0(sK1,X0_44),sK1)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(X0_44,sK1) ),
    inference(subtyping,[status(esa)],[c_397])).

cnf(c_2250,plain,
    ( v3_pre_topc(sK0(sK1,k3_subset_1(u1_struct_0(sK1),X0_44)),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0_44),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0_44),sK1) ),
    inference(instantiation,[status(thm)],[c_1711])).

cnf(c_2252,plain,
    ( v3_pre_topc(sK0(sK1,k3_subset_1(u1_struct_0(sK1),sK2)),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_2250])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | v2_tops_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | v2_tops_1(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | v2_tops_1(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_1709,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0_44),sK1)
    | v2_tops_1(X0_44,sK1) ),
    inference(subtyping,[status(esa)],[c_451])).

cnf(c_1779,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0_44),sK1) != iProver_top
    | v2_tops_1(X0_44,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1709])).

cnf(c_1781,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
    | v2_tops_1(sK2,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_1780,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v2_tops_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2765,c_2689,c_2658,c_2636,c_2634,c_2520,c_2496,c_2276,c_2275,c_2272,c_2267,c_2258,c_2252,c_1781,c_1780,c_21,c_16])).


%------------------------------------------------------------------------------
