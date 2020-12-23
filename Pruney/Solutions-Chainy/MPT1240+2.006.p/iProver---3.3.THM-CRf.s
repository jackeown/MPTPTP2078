%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:58 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  155 (1291 expanded)
%              Number of clauses        :   88 ( 306 expanded)
%              Number of leaves         :   17 ( 320 expanded)
%              Depth                    :   27
%              Number of atoms          :  545 (11212 expanded)
%              Number of equality atoms :  117 ( 233 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK3)
        & r1_tarski(sK3,X2)
        & v3_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
              ( ~ r2_hidden(sK1,X3)
              | ~ r1_tarski(X3,sK2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK1,k1_tops_1(X0,sK2)) )
        & ( ? [X4] :
              ( r2_hidden(sK1,X4)
              & r1_tarski(X4,sK2)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK1,k1_tops_1(X0,sK2)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f43,f42,f41])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1158,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1159,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_1317,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_1318,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1317])).

cnf(c_19,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(X0,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_300,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_301,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_301,c_25])).

cnf(c_306,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_305])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(X0,sK2)
    | k1_tops_1(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_306])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_407])).

cnf(c_1323,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_1324,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_1373,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1159,c_29,c_30,c_1318,c_1324])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_1157,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1167,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2122,plain,
    ( k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_1167])).

cnf(c_5905,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1373,c_2122])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_430,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_431,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_376,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_377,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_493,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) = X1
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_431,c_377])).

cnf(c_494,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_506,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_494,c_8])).

cnf(c_22,negated_conjecture,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | sK3 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_506,c_22])).

cnf(c_543,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_545,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_23])).

cnf(c_1152,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_2172,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1152,c_24,c_545,c_1317,c_1323])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_1154,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_2012,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_1373,c_1154])).

cnf(c_2175,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_2172,c_2012])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1162,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2689,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1373,c_1162])).

cnf(c_3102,plain,
    ( k1_tops_1(sK0,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2175,c_2689])).

cnf(c_5933,plain,
    ( k2_xboole_0(sK3,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5905,c_3102])).

cnf(c_8252,plain,
    ( k2_xboole_0(sK3,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2)
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_5933])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8298,plain,
    ( k2_xboole_0(sK3,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8252,c_29,c_32,c_1318,c_1324])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1161,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_33,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1367,plain,
    ( r2_hidden(sK1,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1161,c_29,c_33,c_1318,c_1324])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1166,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k2_tarski(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3244,plain,
    ( k2_xboole_0(k2_tarski(X0,X1),X2) = X2
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1167])).

cnf(c_12763,plain,
    ( k2_xboole_0(k2_tarski(sK1,X0),sK3) = sK3
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_3244])).

cnf(c_13279,plain,
    ( k2_xboole_0(k2_tarski(sK1,sK1),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1367,c_12763])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1169,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1168,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2301,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1168])).

cnf(c_4231,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2301,c_1168])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1165,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4953,plain,
    ( r2_hidden(X0,k2_xboole_0(k2_xboole_0(k2_tarski(X1,X0),X2),X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4231,c_1165])).

cnf(c_13327,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13279,c_4953])).

cnf(c_13483,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8298,c_13327])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13483,c_1324,c_1318,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:35:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.39/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/0.93  
% 3.39/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/0.93  
% 3.39/0.93  ------  iProver source info
% 3.39/0.93  
% 3.39/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.39/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/0.93  git: non_committed_changes: false
% 3.39/0.93  git: last_make_outside_of_git: false
% 3.39/0.93  
% 3.39/0.93  ------ 
% 3.39/0.93  
% 3.39/0.93  ------ Input Options
% 3.39/0.93  
% 3.39/0.93  --out_options                           all
% 3.39/0.93  --tptp_safe_out                         true
% 3.39/0.93  --problem_path                          ""
% 3.39/0.93  --include_path                          ""
% 3.39/0.93  --clausifier                            res/vclausify_rel
% 3.39/0.93  --clausifier_options                    --mode clausify
% 3.39/0.93  --stdin                                 false
% 3.39/0.93  --stats_out                             all
% 3.39/0.93  
% 3.39/0.93  ------ General Options
% 3.39/0.93  
% 3.39/0.93  --fof                                   false
% 3.39/0.93  --time_out_real                         305.
% 3.39/0.93  --time_out_virtual                      -1.
% 3.39/0.93  --symbol_type_check                     false
% 3.39/0.93  --clausify_out                          false
% 3.39/0.93  --sig_cnt_out                           false
% 3.39/0.93  --trig_cnt_out                          false
% 3.39/0.93  --trig_cnt_out_tolerance                1.
% 3.39/0.93  --trig_cnt_out_sk_spl                   false
% 3.39/0.93  --abstr_cl_out                          false
% 3.39/0.93  
% 3.39/0.93  ------ Global Options
% 3.39/0.93  
% 3.39/0.93  --schedule                              default
% 3.39/0.93  --add_important_lit                     false
% 3.39/0.93  --prop_solver_per_cl                    1000
% 3.39/0.93  --min_unsat_core                        false
% 3.39/0.93  --soft_assumptions                      false
% 3.39/0.93  --soft_lemma_size                       3
% 3.39/0.93  --prop_impl_unit_size                   0
% 3.39/0.93  --prop_impl_unit                        []
% 3.39/0.93  --share_sel_clauses                     true
% 3.39/0.93  --reset_solvers                         false
% 3.39/0.93  --bc_imp_inh                            [conj_cone]
% 3.39/0.93  --conj_cone_tolerance                   3.
% 3.39/0.93  --extra_neg_conj                        none
% 3.39/0.93  --large_theory_mode                     true
% 3.39/0.93  --prolific_symb_bound                   200
% 3.39/0.93  --lt_threshold                          2000
% 3.39/0.93  --clause_weak_htbl                      true
% 3.39/0.93  --gc_record_bc_elim                     false
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing Options
% 3.39/0.93  
% 3.39/0.93  --preprocessing_flag                    true
% 3.39/0.93  --time_out_prep_mult                    0.1
% 3.39/0.93  --splitting_mode                        input
% 3.39/0.93  --splitting_grd                         true
% 3.39/0.93  --splitting_cvd                         false
% 3.39/0.93  --splitting_cvd_svl                     false
% 3.39/0.93  --splitting_nvd                         32
% 3.39/0.93  --sub_typing                            true
% 3.39/0.93  --prep_gs_sim                           true
% 3.39/0.93  --prep_unflatten                        true
% 3.39/0.93  --prep_res_sim                          true
% 3.39/0.93  --prep_upred                            true
% 3.39/0.93  --prep_sem_filter                       exhaustive
% 3.39/0.93  --prep_sem_filter_out                   false
% 3.39/0.93  --pred_elim                             true
% 3.39/0.93  --res_sim_input                         true
% 3.39/0.93  --eq_ax_congr_red                       true
% 3.39/0.93  --pure_diseq_elim                       true
% 3.39/0.93  --brand_transform                       false
% 3.39/0.93  --non_eq_to_eq                          false
% 3.39/0.93  --prep_def_merge                        true
% 3.39/0.93  --prep_def_merge_prop_impl              false
% 3.39/0.93  --prep_def_merge_mbd                    true
% 3.39/0.93  --prep_def_merge_tr_red                 false
% 3.39/0.93  --prep_def_merge_tr_cl                  false
% 3.39/0.93  --smt_preprocessing                     true
% 3.39/0.93  --smt_ac_axioms                         fast
% 3.39/0.93  --preprocessed_out                      false
% 3.39/0.93  --preprocessed_stats                    false
% 3.39/0.93  
% 3.39/0.93  ------ Abstraction refinement Options
% 3.39/0.93  
% 3.39/0.93  --abstr_ref                             []
% 3.39/0.93  --abstr_ref_prep                        false
% 3.39/0.93  --abstr_ref_until_sat                   false
% 3.39/0.93  --abstr_ref_sig_restrict                funpre
% 3.39/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.93  --abstr_ref_under                       []
% 3.39/0.93  
% 3.39/0.93  ------ SAT Options
% 3.39/0.93  
% 3.39/0.93  --sat_mode                              false
% 3.39/0.93  --sat_fm_restart_options                ""
% 3.39/0.93  --sat_gr_def                            false
% 3.39/0.93  --sat_epr_types                         true
% 3.39/0.93  --sat_non_cyclic_types                  false
% 3.39/0.93  --sat_finite_models                     false
% 3.39/0.93  --sat_fm_lemmas                         false
% 3.39/0.93  --sat_fm_prep                           false
% 3.39/0.93  --sat_fm_uc_incr                        true
% 3.39/0.93  --sat_out_model                         small
% 3.39/0.93  --sat_out_clauses                       false
% 3.39/0.93  
% 3.39/0.93  ------ QBF Options
% 3.39/0.93  
% 3.39/0.93  --qbf_mode                              false
% 3.39/0.93  --qbf_elim_univ                         false
% 3.39/0.93  --qbf_dom_inst                          none
% 3.39/0.93  --qbf_dom_pre_inst                      false
% 3.39/0.93  --qbf_sk_in                             false
% 3.39/0.93  --qbf_pred_elim                         true
% 3.39/0.93  --qbf_split                             512
% 3.39/0.93  
% 3.39/0.93  ------ BMC1 Options
% 3.39/0.93  
% 3.39/0.93  --bmc1_incremental                      false
% 3.39/0.93  --bmc1_axioms                           reachable_all
% 3.39/0.93  --bmc1_min_bound                        0
% 3.39/0.93  --bmc1_max_bound                        -1
% 3.39/0.93  --bmc1_max_bound_default                -1
% 3.39/0.93  --bmc1_symbol_reachability              true
% 3.39/0.93  --bmc1_property_lemmas                  false
% 3.39/0.93  --bmc1_k_induction                      false
% 3.39/0.93  --bmc1_non_equiv_states                 false
% 3.39/0.93  --bmc1_deadlock                         false
% 3.39/0.93  --bmc1_ucm                              false
% 3.39/0.93  --bmc1_add_unsat_core                   none
% 3.39/0.93  --bmc1_unsat_core_children              false
% 3.39/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.93  --bmc1_out_stat                         full
% 3.39/0.93  --bmc1_ground_init                      false
% 3.39/0.93  --bmc1_pre_inst_next_state              false
% 3.39/0.93  --bmc1_pre_inst_state                   false
% 3.39/0.93  --bmc1_pre_inst_reach_state             false
% 3.39/0.93  --bmc1_out_unsat_core                   false
% 3.39/0.93  --bmc1_aig_witness_out                  false
% 3.39/0.93  --bmc1_verbose                          false
% 3.39/0.93  --bmc1_dump_clauses_tptp                false
% 3.39/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.93  --bmc1_dump_file                        -
% 3.39/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.93  --bmc1_ucm_extend_mode                  1
% 3.39/0.93  --bmc1_ucm_init_mode                    2
% 3.39/0.93  --bmc1_ucm_cone_mode                    none
% 3.39/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.93  --bmc1_ucm_relax_model                  4
% 3.39/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.93  --bmc1_ucm_layered_model                none
% 3.39/0.93  --bmc1_ucm_max_lemma_size               10
% 3.39/0.93  
% 3.39/0.93  ------ AIG Options
% 3.39/0.93  
% 3.39/0.93  --aig_mode                              false
% 3.39/0.93  
% 3.39/0.93  ------ Instantiation Options
% 3.39/0.93  
% 3.39/0.93  --instantiation_flag                    true
% 3.39/0.93  --inst_sos_flag                         false
% 3.39/0.93  --inst_sos_phase                        true
% 3.39/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.93  --inst_lit_sel_side                     num_symb
% 3.39/0.93  --inst_solver_per_active                1400
% 3.39/0.93  --inst_solver_calls_frac                1.
% 3.39/0.93  --inst_passive_queue_type               priority_queues
% 3.39/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.93  --inst_passive_queues_freq              [25;2]
% 3.39/0.93  --inst_dismatching                      true
% 3.39/0.93  --inst_eager_unprocessed_to_passive     true
% 3.39/0.93  --inst_prop_sim_given                   true
% 3.39/0.93  --inst_prop_sim_new                     false
% 3.39/0.93  --inst_subs_new                         false
% 3.39/0.93  --inst_eq_res_simp                      false
% 3.39/0.93  --inst_subs_given                       false
% 3.39/0.93  --inst_orphan_elimination               true
% 3.39/0.93  --inst_learning_loop_flag               true
% 3.39/0.93  --inst_learning_start                   3000
% 3.39/0.93  --inst_learning_factor                  2
% 3.39/0.93  --inst_start_prop_sim_after_learn       3
% 3.39/0.93  --inst_sel_renew                        solver
% 3.39/0.93  --inst_lit_activity_flag                true
% 3.39/0.93  --inst_restr_to_given                   false
% 3.39/0.93  --inst_activity_threshold               500
% 3.39/0.93  --inst_out_proof                        true
% 3.39/0.93  
% 3.39/0.93  ------ Resolution Options
% 3.39/0.93  
% 3.39/0.93  --resolution_flag                       true
% 3.39/0.93  --res_lit_sel                           adaptive
% 3.39/0.93  --res_lit_sel_side                      none
% 3.39/0.93  --res_ordering                          kbo
% 3.39/0.93  --res_to_prop_solver                    active
% 3.39/0.93  --res_prop_simpl_new                    false
% 3.39/0.93  --res_prop_simpl_given                  true
% 3.39/0.93  --res_passive_queue_type                priority_queues
% 3.39/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.93  --res_passive_queues_freq               [15;5]
% 3.39/0.93  --res_forward_subs                      full
% 3.39/0.93  --res_backward_subs                     full
% 3.39/0.93  --res_forward_subs_resolution           true
% 3.39/0.93  --res_backward_subs_resolution          true
% 3.39/0.93  --res_orphan_elimination                true
% 3.39/0.93  --res_time_limit                        2.
% 3.39/0.93  --res_out_proof                         true
% 3.39/0.93  
% 3.39/0.93  ------ Superposition Options
% 3.39/0.93  
% 3.39/0.93  --superposition_flag                    true
% 3.39/0.93  --sup_passive_queue_type                priority_queues
% 3.39/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.93  --demod_completeness_check              fast
% 3.39/0.93  --demod_use_ground                      true
% 3.39/0.93  --sup_to_prop_solver                    passive
% 3.39/0.93  --sup_prop_simpl_new                    true
% 3.39/0.93  --sup_prop_simpl_given                  true
% 3.39/0.93  --sup_fun_splitting                     false
% 3.39/0.93  --sup_smt_interval                      50000
% 3.39/0.93  
% 3.39/0.93  ------ Superposition Simplification Setup
% 3.39/0.93  
% 3.39/0.93  --sup_indices_passive                   []
% 3.39/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_full_bw                           [BwDemod]
% 3.39/0.93  --sup_immed_triv                        [TrivRules]
% 3.39/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_immed_bw_main                     []
% 3.39/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.93  
% 3.39/0.93  ------ Combination Options
% 3.39/0.93  
% 3.39/0.93  --comb_res_mult                         3
% 3.39/0.93  --comb_sup_mult                         2
% 3.39/0.93  --comb_inst_mult                        10
% 3.39/0.93  
% 3.39/0.93  ------ Debug Options
% 3.39/0.93  
% 3.39/0.93  --dbg_backtrace                         false
% 3.39/0.93  --dbg_dump_prop_clauses                 false
% 3.39/0.93  --dbg_dump_prop_clauses_file            -
% 3.39/0.93  --dbg_out_stat                          false
% 3.39/0.93  ------ Parsing...
% 3.39/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/0.93  ------ Proving...
% 3.39/0.93  ------ Problem Properties 
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  clauses                                 21
% 3.39/0.93  conjectures                             4
% 3.39/0.93  EPR                                     2
% 3.39/0.93  Horn                                    17
% 3.39/0.93  unary                                   2
% 3.39/0.93  binary                                  14
% 3.39/0.93  lits                                    49
% 3.39/0.93  lits eq                                 7
% 3.39/0.93  fd_pure                                 0
% 3.39/0.93  fd_pseudo                               0
% 3.39/0.93  fd_cond                                 0
% 3.39/0.93  fd_pseudo_cond                          1
% 3.39/0.93  AC symbols                              0
% 3.39/0.93  
% 3.39/0.93  ------ Schedule dynamic 5 is on 
% 3.39/0.93  
% 3.39/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  ------ 
% 3.39/0.93  Current options:
% 3.39/0.93  ------ 
% 3.39/0.93  
% 3.39/0.93  ------ Input Options
% 3.39/0.93  
% 3.39/0.93  --out_options                           all
% 3.39/0.93  --tptp_safe_out                         true
% 3.39/0.93  --problem_path                          ""
% 3.39/0.93  --include_path                          ""
% 3.39/0.93  --clausifier                            res/vclausify_rel
% 3.39/0.93  --clausifier_options                    --mode clausify
% 3.39/0.93  --stdin                                 false
% 3.39/0.93  --stats_out                             all
% 3.39/0.93  
% 3.39/0.93  ------ General Options
% 3.39/0.93  
% 3.39/0.93  --fof                                   false
% 3.39/0.93  --time_out_real                         305.
% 3.39/0.93  --time_out_virtual                      -1.
% 3.39/0.93  --symbol_type_check                     false
% 3.39/0.93  --clausify_out                          false
% 3.39/0.93  --sig_cnt_out                           false
% 3.39/0.93  --trig_cnt_out                          false
% 3.39/0.93  --trig_cnt_out_tolerance                1.
% 3.39/0.93  --trig_cnt_out_sk_spl                   false
% 3.39/0.93  --abstr_cl_out                          false
% 3.39/0.93  
% 3.39/0.93  ------ Global Options
% 3.39/0.93  
% 3.39/0.93  --schedule                              default
% 3.39/0.93  --add_important_lit                     false
% 3.39/0.93  --prop_solver_per_cl                    1000
% 3.39/0.93  --min_unsat_core                        false
% 3.39/0.93  --soft_assumptions                      false
% 3.39/0.93  --soft_lemma_size                       3
% 3.39/0.93  --prop_impl_unit_size                   0
% 3.39/0.93  --prop_impl_unit                        []
% 3.39/0.93  --share_sel_clauses                     true
% 3.39/0.93  --reset_solvers                         false
% 3.39/0.93  --bc_imp_inh                            [conj_cone]
% 3.39/0.93  --conj_cone_tolerance                   3.
% 3.39/0.93  --extra_neg_conj                        none
% 3.39/0.93  --large_theory_mode                     true
% 3.39/0.93  --prolific_symb_bound                   200
% 3.39/0.93  --lt_threshold                          2000
% 3.39/0.93  --clause_weak_htbl                      true
% 3.39/0.93  --gc_record_bc_elim                     false
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing Options
% 3.39/0.93  
% 3.39/0.93  --preprocessing_flag                    true
% 3.39/0.93  --time_out_prep_mult                    0.1
% 3.39/0.93  --splitting_mode                        input
% 3.39/0.93  --splitting_grd                         true
% 3.39/0.93  --splitting_cvd                         false
% 3.39/0.93  --splitting_cvd_svl                     false
% 3.39/0.93  --splitting_nvd                         32
% 3.39/0.93  --sub_typing                            true
% 3.39/0.93  --prep_gs_sim                           true
% 3.39/0.93  --prep_unflatten                        true
% 3.39/0.93  --prep_res_sim                          true
% 3.39/0.93  --prep_upred                            true
% 3.39/0.93  --prep_sem_filter                       exhaustive
% 3.39/0.93  --prep_sem_filter_out                   false
% 3.39/0.93  --pred_elim                             true
% 3.39/0.93  --res_sim_input                         true
% 3.39/0.93  --eq_ax_congr_red                       true
% 3.39/0.93  --pure_diseq_elim                       true
% 3.39/0.93  --brand_transform                       false
% 3.39/0.93  --non_eq_to_eq                          false
% 3.39/0.93  --prep_def_merge                        true
% 3.39/0.93  --prep_def_merge_prop_impl              false
% 3.39/0.93  --prep_def_merge_mbd                    true
% 3.39/0.93  --prep_def_merge_tr_red                 false
% 3.39/0.93  --prep_def_merge_tr_cl                  false
% 3.39/0.93  --smt_preprocessing                     true
% 3.39/0.93  --smt_ac_axioms                         fast
% 3.39/0.93  --preprocessed_out                      false
% 3.39/0.93  --preprocessed_stats                    false
% 3.39/0.93  
% 3.39/0.93  ------ Abstraction refinement Options
% 3.39/0.93  
% 3.39/0.93  --abstr_ref                             []
% 3.39/0.93  --abstr_ref_prep                        false
% 3.39/0.93  --abstr_ref_until_sat                   false
% 3.39/0.93  --abstr_ref_sig_restrict                funpre
% 3.39/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.93  --abstr_ref_under                       []
% 3.39/0.93  
% 3.39/0.93  ------ SAT Options
% 3.39/0.93  
% 3.39/0.93  --sat_mode                              false
% 3.39/0.93  --sat_fm_restart_options                ""
% 3.39/0.93  --sat_gr_def                            false
% 3.39/0.93  --sat_epr_types                         true
% 3.39/0.93  --sat_non_cyclic_types                  false
% 3.39/0.93  --sat_finite_models                     false
% 3.39/0.93  --sat_fm_lemmas                         false
% 3.39/0.93  --sat_fm_prep                           false
% 3.39/0.93  --sat_fm_uc_incr                        true
% 3.39/0.93  --sat_out_model                         small
% 3.39/0.93  --sat_out_clauses                       false
% 3.39/0.93  
% 3.39/0.93  ------ QBF Options
% 3.39/0.93  
% 3.39/0.93  --qbf_mode                              false
% 3.39/0.93  --qbf_elim_univ                         false
% 3.39/0.93  --qbf_dom_inst                          none
% 3.39/0.93  --qbf_dom_pre_inst                      false
% 3.39/0.93  --qbf_sk_in                             false
% 3.39/0.93  --qbf_pred_elim                         true
% 3.39/0.93  --qbf_split                             512
% 3.39/0.93  
% 3.39/0.93  ------ BMC1 Options
% 3.39/0.93  
% 3.39/0.93  --bmc1_incremental                      false
% 3.39/0.93  --bmc1_axioms                           reachable_all
% 3.39/0.93  --bmc1_min_bound                        0
% 3.39/0.93  --bmc1_max_bound                        -1
% 3.39/0.93  --bmc1_max_bound_default                -1
% 3.39/0.93  --bmc1_symbol_reachability              true
% 3.39/0.93  --bmc1_property_lemmas                  false
% 3.39/0.93  --bmc1_k_induction                      false
% 3.39/0.93  --bmc1_non_equiv_states                 false
% 3.39/0.93  --bmc1_deadlock                         false
% 3.39/0.93  --bmc1_ucm                              false
% 3.39/0.93  --bmc1_add_unsat_core                   none
% 3.39/0.93  --bmc1_unsat_core_children              false
% 3.39/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.93  --bmc1_out_stat                         full
% 3.39/0.93  --bmc1_ground_init                      false
% 3.39/0.93  --bmc1_pre_inst_next_state              false
% 3.39/0.93  --bmc1_pre_inst_state                   false
% 3.39/0.93  --bmc1_pre_inst_reach_state             false
% 3.39/0.93  --bmc1_out_unsat_core                   false
% 3.39/0.93  --bmc1_aig_witness_out                  false
% 3.39/0.93  --bmc1_verbose                          false
% 3.39/0.93  --bmc1_dump_clauses_tptp                false
% 3.39/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.93  --bmc1_dump_file                        -
% 3.39/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.93  --bmc1_ucm_extend_mode                  1
% 3.39/0.93  --bmc1_ucm_init_mode                    2
% 3.39/0.93  --bmc1_ucm_cone_mode                    none
% 3.39/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.93  --bmc1_ucm_relax_model                  4
% 3.39/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.93  --bmc1_ucm_layered_model                none
% 3.39/0.93  --bmc1_ucm_max_lemma_size               10
% 3.39/0.93  
% 3.39/0.93  ------ AIG Options
% 3.39/0.93  
% 3.39/0.93  --aig_mode                              false
% 3.39/0.93  
% 3.39/0.93  ------ Instantiation Options
% 3.39/0.93  
% 3.39/0.93  --instantiation_flag                    true
% 3.39/0.93  --inst_sos_flag                         false
% 3.39/0.93  --inst_sos_phase                        true
% 3.39/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.93  --inst_lit_sel_side                     none
% 3.39/0.93  --inst_solver_per_active                1400
% 3.39/0.93  --inst_solver_calls_frac                1.
% 3.39/0.93  --inst_passive_queue_type               priority_queues
% 3.39/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.93  --inst_passive_queues_freq              [25;2]
% 3.39/0.93  --inst_dismatching                      true
% 3.39/0.93  --inst_eager_unprocessed_to_passive     true
% 3.39/0.93  --inst_prop_sim_given                   true
% 3.39/0.93  --inst_prop_sim_new                     false
% 3.39/0.93  --inst_subs_new                         false
% 3.39/0.93  --inst_eq_res_simp                      false
% 3.39/0.93  --inst_subs_given                       false
% 3.39/0.93  --inst_orphan_elimination               true
% 3.39/0.93  --inst_learning_loop_flag               true
% 3.39/0.93  --inst_learning_start                   3000
% 3.39/0.93  --inst_learning_factor                  2
% 3.39/0.93  --inst_start_prop_sim_after_learn       3
% 3.39/0.93  --inst_sel_renew                        solver
% 3.39/0.93  --inst_lit_activity_flag                true
% 3.39/0.93  --inst_restr_to_given                   false
% 3.39/0.93  --inst_activity_threshold               500
% 3.39/0.93  --inst_out_proof                        true
% 3.39/0.93  
% 3.39/0.93  ------ Resolution Options
% 3.39/0.93  
% 3.39/0.93  --resolution_flag                       false
% 3.39/0.93  --res_lit_sel                           adaptive
% 3.39/0.93  --res_lit_sel_side                      none
% 3.39/0.93  --res_ordering                          kbo
% 3.39/0.93  --res_to_prop_solver                    active
% 3.39/0.93  --res_prop_simpl_new                    false
% 3.39/0.93  --res_prop_simpl_given                  true
% 3.39/0.93  --res_passive_queue_type                priority_queues
% 3.39/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.93  --res_passive_queues_freq               [15;5]
% 3.39/0.93  --res_forward_subs                      full
% 3.39/0.93  --res_backward_subs                     full
% 3.39/0.93  --res_forward_subs_resolution           true
% 3.39/0.93  --res_backward_subs_resolution          true
% 3.39/0.93  --res_orphan_elimination                true
% 3.39/0.93  --res_time_limit                        2.
% 3.39/0.93  --res_out_proof                         true
% 3.39/0.93  
% 3.39/0.93  ------ Superposition Options
% 3.39/0.93  
% 3.39/0.93  --superposition_flag                    true
% 3.39/0.93  --sup_passive_queue_type                priority_queues
% 3.39/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.93  --demod_completeness_check              fast
% 3.39/0.93  --demod_use_ground                      true
% 3.39/0.93  --sup_to_prop_solver                    passive
% 3.39/0.93  --sup_prop_simpl_new                    true
% 3.39/0.93  --sup_prop_simpl_given                  true
% 3.39/0.93  --sup_fun_splitting                     false
% 3.39/0.93  --sup_smt_interval                      50000
% 3.39/0.93  
% 3.39/0.93  ------ Superposition Simplification Setup
% 3.39/0.93  
% 3.39/0.93  --sup_indices_passive                   []
% 3.39/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_full_bw                           [BwDemod]
% 3.39/0.93  --sup_immed_triv                        [TrivRules]
% 3.39/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_immed_bw_main                     []
% 3.39/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.93  
% 3.39/0.93  ------ Combination Options
% 3.39/0.93  
% 3.39/0.93  --comb_res_mult                         3
% 3.39/0.93  --comb_sup_mult                         2
% 3.39/0.93  --comb_inst_mult                        10
% 3.39/0.93  
% 3.39/0.93  ------ Debug Options
% 3.39/0.93  
% 3.39/0.93  --dbg_backtrace                         false
% 3.39/0.93  --dbg_dump_prop_clauses                 false
% 3.39/0.93  --dbg_dump_prop_clauses_file            -
% 3.39/0.93  --dbg_out_stat                          false
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  ------ Proving...
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  % SZS status Theorem for theBenchmark.p
% 3.39/0.93  
% 3.39/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/0.93  
% 3.39/0.93  fof(f14,conjecture,(
% 3.39/0.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f15,negated_conjecture,(
% 3.39/0.93    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.39/0.93    inference(negated_conjecture,[],[f14])).
% 3.39/0.93  
% 3.39/0.93  fof(f31,plain,(
% 3.39/0.93    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.39/0.93    inference(ennf_transformation,[],[f15])).
% 3.39/0.93  
% 3.39/0.93  fof(f32,plain,(
% 3.39/0.93    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.39/0.93    inference(flattening,[],[f31])).
% 3.39/0.93  
% 3.39/0.93  fof(f38,plain,(
% 3.39/0.93    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.39/0.93    inference(nnf_transformation,[],[f32])).
% 3.39/0.93  
% 3.39/0.93  fof(f39,plain,(
% 3.39/0.93    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.39/0.93    inference(flattening,[],[f38])).
% 3.39/0.93  
% 3.39/0.93  fof(f40,plain,(
% 3.39/0.93    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.39/0.93    inference(rectify,[],[f39])).
% 3.39/0.93  
% 3.39/0.93  fof(f43,plain,(
% 3.39/0.93    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3) & r1_tarski(sK3,X2) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.39/0.93    introduced(choice_axiom,[])).
% 3.39/0.93  
% 3.39/0.93  fof(f42,plain,(
% 3.39/0.93    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK1,k1_tops_1(X0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK1,k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.39/0.93    introduced(choice_axiom,[])).
% 3.39/0.93  
% 3.39/0.93  fof(f41,plain,(
% 3.39/0.93    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.39/0.93    introduced(choice_axiom,[])).
% 3.39/0.93  
% 3.39/0.93  fof(f44,plain,(
% 3.39/0.93    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.39/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f43,f42,f41])).
% 3.39/0.93  
% 3.39/0.93  fof(f66,plain,(
% 3.39/0.93    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.39/0.93    inference(cnf_transformation,[],[f44])).
% 3.39/0.93  
% 3.39/0.93  fof(f67,plain,(
% 3.39/0.93    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.39/0.93    inference(cnf_transformation,[],[f44])).
% 3.39/0.93  
% 3.39/0.93  fof(f12,axiom,(
% 3.39/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f28,plain,(
% 3.39/0.93    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.39/0.93    inference(ennf_transformation,[],[f12])).
% 3.39/0.93  
% 3.39/0.93  fof(f62,plain,(
% 3.39/0.93    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f28])).
% 3.39/0.93  
% 3.39/0.93  fof(f65,plain,(
% 3.39/0.93    l1_pre_topc(sK0)),
% 3.39/0.93    inference(cnf_transformation,[],[f44])).
% 3.39/0.93  
% 3.39/0.93  fof(f71,plain,(
% 3.39/0.93    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 3.39/0.93    inference(cnf_transformation,[],[f44])).
% 3.39/0.93  
% 3.39/0.93  fof(f10,axiom,(
% 3.39/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f25,plain,(
% 3.39/0.93    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.39/0.93    inference(ennf_transformation,[],[f10])).
% 3.39/0.93  
% 3.39/0.93  fof(f26,plain,(
% 3.39/0.93    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.39/0.93    inference(flattening,[],[f25])).
% 3.39/0.93  
% 3.39/0.93  fof(f59,plain,(
% 3.39/0.93    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f26])).
% 3.39/0.93  
% 3.39/0.93  fof(f64,plain,(
% 3.39/0.93    v2_pre_topc(sK0)),
% 3.39/0.93    inference(cnf_transformation,[],[f44])).
% 3.39/0.93  
% 3.39/0.93  fof(f9,axiom,(
% 3.39/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f23,plain,(
% 3.39/0.93    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.39/0.93    inference(ennf_transformation,[],[f9])).
% 3.39/0.93  
% 3.39/0.93  fof(f24,plain,(
% 3.39/0.93    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.39/0.93    inference(flattening,[],[f23])).
% 3.39/0.93  
% 3.39/0.93  fof(f58,plain,(
% 3.39/0.93    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f24])).
% 3.39/0.93  
% 3.39/0.93  fof(f13,axiom,(
% 3.39/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f29,plain,(
% 3.39/0.93    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.39/0.93    inference(ennf_transformation,[],[f13])).
% 3.39/0.93  
% 3.39/0.93  fof(f30,plain,(
% 3.39/0.93    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.39/0.93    inference(flattening,[],[f29])).
% 3.39/0.93  
% 3.39/0.93  fof(f63,plain,(
% 3.39/0.93    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f30])).
% 3.39/0.93  
% 3.39/0.93  fof(f3,axiom,(
% 3.39/0.93    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f17,plain,(
% 3.39/0.93    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.39/0.93    inference(ennf_transformation,[],[f3])).
% 3.39/0.93  
% 3.39/0.93  fof(f49,plain,(
% 3.39/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f17])).
% 3.39/0.93  
% 3.39/0.93  fof(f7,axiom,(
% 3.39/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f20,plain,(
% 3.39/0.93    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.39/0.93    inference(ennf_transformation,[],[f7])).
% 3.39/0.93  
% 3.39/0.93  fof(f21,plain,(
% 3.39/0.93    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.39/0.93    inference(flattening,[],[f20])).
% 3.39/0.93  
% 3.39/0.93  fof(f55,plain,(
% 3.39/0.93    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f21])).
% 3.39/0.93  
% 3.39/0.93  fof(f11,axiom,(
% 3.39/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f27,plain,(
% 3.39/0.93    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.39/0.93    inference(ennf_transformation,[],[f11])).
% 3.39/0.93  
% 3.39/0.93  fof(f37,plain,(
% 3.39/0.93    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.39/0.93    inference(nnf_transformation,[],[f27])).
% 3.39/0.93  
% 3.39/0.93  fof(f60,plain,(
% 3.39/0.93    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f37])).
% 3.39/0.93  
% 3.39/0.93  fof(f5,axiom,(
% 3.39/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f18,plain,(
% 3.39/0.93    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.39/0.93    inference(ennf_transformation,[],[f5])).
% 3.39/0.93  
% 3.39/0.93  fof(f53,plain,(
% 3.39/0.93    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.39/0.93    inference(cnf_transformation,[],[f18])).
% 3.39/0.93  
% 3.39/0.93  fof(f68,plain,(
% 3.39/0.93    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.39/0.93    inference(cnf_transformation,[],[f44])).
% 3.39/0.93  
% 3.39/0.93  fof(f8,axiom,(
% 3.39/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f22,plain,(
% 3.39/0.93    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.39/0.93    inference(ennf_transformation,[],[f8])).
% 3.39/0.93  
% 3.39/0.93  fof(f57,plain,(
% 3.39/0.93    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f22])).
% 3.39/0.93  
% 3.39/0.93  fof(f6,axiom,(
% 3.39/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f19,plain,(
% 3.39/0.93    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.39/0.93    inference(ennf_transformation,[],[f6])).
% 3.39/0.93  
% 3.39/0.93  fof(f54,plain,(
% 3.39/0.93    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.39/0.93    inference(cnf_transformation,[],[f19])).
% 3.39/0.93  
% 3.39/0.93  fof(f69,plain,(
% 3.39/0.93    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.39/0.93    inference(cnf_transformation,[],[f44])).
% 3.39/0.93  
% 3.39/0.93  fof(f70,plain,(
% 3.39/0.93    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.39/0.93    inference(cnf_transformation,[],[f44])).
% 3.39/0.93  
% 3.39/0.93  fof(f4,axiom,(
% 3.39/0.93    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f35,plain,(
% 3.39/0.93    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.39/0.93    inference(nnf_transformation,[],[f4])).
% 3.39/0.93  
% 3.39/0.93  fof(f36,plain,(
% 3.39/0.93    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.39/0.93    inference(flattening,[],[f35])).
% 3.39/0.93  
% 3.39/0.93  fof(f52,plain,(
% 3.39/0.93    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f36])).
% 3.39/0.93  
% 3.39/0.93  fof(f1,axiom,(
% 3.39/0.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f33,plain,(
% 3.39/0.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.39/0.93    inference(nnf_transformation,[],[f1])).
% 3.39/0.93  
% 3.39/0.93  fof(f34,plain,(
% 3.39/0.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.39/0.93    inference(flattening,[],[f33])).
% 3.39/0.93  
% 3.39/0.93  fof(f45,plain,(
% 3.39/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.39/0.93    inference(cnf_transformation,[],[f34])).
% 3.39/0.93  
% 3.39/0.93  fof(f73,plain,(
% 3.39/0.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.39/0.93    inference(equality_resolution,[],[f45])).
% 3.39/0.93  
% 3.39/0.93  fof(f2,axiom,(
% 3.39/0.93    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.39/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.93  
% 3.39/0.93  fof(f16,plain,(
% 3.39/0.93    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.39/0.93    inference(ennf_transformation,[],[f2])).
% 3.39/0.93  
% 3.39/0.93  fof(f48,plain,(
% 3.39/0.93    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f16])).
% 3.39/0.93  
% 3.39/0.93  fof(f51,plain,(
% 3.39/0.93    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.39/0.93    inference(cnf_transformation,[],[f36])).
% 3.39/0.93  
% 3.39/0.93  cnf(c_24,negated_conjecture,
% 3.39/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.39/0.93      inference(cnf_transformation,[],[f66]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1158,plain,
% 3.39/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_23,negated_conjecture,
% 3.39/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 3.39/0.93      inference(cnf_transformation,[],[f67]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1159,plain,
% 3.39/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.39/0.93      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_29,plain,
% 3.39/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_30,plain,
% 3.39/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.39/0.93      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_17,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.39/0.93      | ~ l1_pre_topc(X1) ),
% 3.39/0.93      inference(cnf_transformation,[],[f62]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_25,negated_conjecture,
% 3.39/0.93      ( l1_pre_topc(sK0) ),
% 3.39/0.93      inference(cnf_transformation,[],[f65]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_364,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.39/0.93      | sK0 != X1 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_365,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_364]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1317,plain,
% 3.39/0.93      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 3.39/0.93      inference(instantiation,[status(thm)],[c_365]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1318,plain,
% 3.39/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.39/0.93      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_1317]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_19,negated_conjecture,
% 3.39/0.93      ( ~ v3_pre_topc(X0,sK0)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ r2_hidden(sK1,X0)
% 3.39/0.93      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.39/0.93      | ~ r1_tarski(X0,sK2) ),
% 3.39/0.93      inference(cnf_transformation,[],[f71]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_14,plain,
% 3.39/0.93      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.39/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.39/0.93      | ~ l1_pre_topc(X0)
% 3.39/0.93      | ~ v2_pre_topc(X0) ),
% 3.39/0.93      inference(cnf_transformation,[],[f59]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_26,negated_conjecture,
% 3.39/0.93      ( v2_pre_topc(sK0) ),
% 3.39/0.93      inference(cnf_transformation,[],[f64]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_300,plain,
% 3.39/0.93      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.39/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.39/0.93      | ~ l1_pre_topc(X0)
% 3.39/0.93      | sK0 != X0 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_301,plain,
% 3.39/0.93      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ l1_pre_topc(sK0) ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_300]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_305,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 3.39/0.93      inference(global_propositional_subsumption,
% 3.39/0.93                [status(thm)],
% 3.39/0.93                [c_301,c_25]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_306,plain,
% 3.39/0.93      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.39/0.93      inference(renaming,[status(thm)],[c_305]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_576,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ r2_hidden(sK1,X0)
% 3.39/0.93      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.39/0.93      | ~ r1_tarski(X0,sK2)
% 3.39/0.93      | k1_tops_1(sK0,X1) != X0
% 3.39/0.93      | sK0 != sK0 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_19,c_306]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_577,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.39/0.93      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.39/0.93      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_576]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_13,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | ~ l1_pre_topc(X1) ),
% 3.39/0.93      inference(cnf_transformation,[],[f58]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_406,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | sK0 != X1 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_407,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_406]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_581,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.39/0.93      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.39/0.93      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 3.39/0.93      inference(global_propositional_subsumption,
% 3.39/0.93                [status(thm)],
% 3.39/0.93                [c_577,c_407]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1323,plain,
% 3.39/0.93      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.39/0.93      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 3.39/0.93      inference(instantiation,[status(thm)],[c_581]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1324,plain,
% 3.39/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.39/0.93      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 3.39/0.93      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1373,plain,
% 3.39/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.39/0.93      inference(global_propositional_subsumption,
% 3.39/0.93                [status(thm)],
% 3.39/0.93                [c_1159,c_29,c_30,c_1318,c_1324]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_18,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | ~ r1_tarski(X0,X2)
% 3.39/0.93      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.39/0.93      | ~ l1_pre_topc(X1) ),
% 3.39/0.93      inference(cnf_transformation,[],[f63]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_346,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | ~ r1_tarski(X0,X2)
% 3.39/0.93      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.39/0.93      | sK0 != X1 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_347,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ r1_tarski(X0,X1)
% 3.39/0.93      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_346]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1157,plain,
% 3.39/0.93      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.39/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.39/0.93      | r1_tarski(X0,X1) != iProver_top
% 3.39/0.93      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_4,plain,
% 3.39/0.93      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.39/0.93      inference(cnf_transformation,[],[f49]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1167,plain,
% 3.39/0.93      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_2122,plain,
% 3.39/0.93      ( k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
% 3.39/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.39/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.39/0.93      | r1_tarski(X0,X1) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_1157,c_1167]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_5905,plain,
% 3.39/0.93      ( k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 3.39/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.39/0.93      | r1_tarski(sK3,X0) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_1373,c_2122]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_11,plain,
% 3.39/0.93      ( ~ v4_pre_topc(X0,X1)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | ~ l1_pre_topc(X1)
% 3.39/0.93      | k2_pre_topc(X1,X0) = X0 ),
% 3.39/0.93      inference(cnf_transformation,[],[f55]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_430,plain,
% 3.39/0.93      ( ~ v4_pre_topc(X0,X1)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | k2_pre_topc(X1,X0) = X0
% 3.39/0.93      | sK0 != X1 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_431,plain,
% 3.39/0.93      ( ~ v4_pre_topc(X0,sK0)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | k2_pre_topc(sK0,X0) = X0 ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_430]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_16,plain,
% 3.39/0.93      ( ~ v3_pre_topc(X0,X1)
% 3.39/0.93      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | ~ l1_pre_topc(X1) ),
% 3.39/0.93      inference(cnf_transformation,[],[f60]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_376,plain,
% 3.39/0.93      ( ~ v3_pre_topc(X0,X1)
% 3.39/0.93      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | sK0 != X1 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_377,plain,
% 3.39/0.93      ( ~ v3_pre_topc(X0,sK0)
% 3.39/0.93      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_376]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_493,plain,
% 3.39/0.93      ( ~ v3_pre_topc(X0,sK0)
% 3.39/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | k2_pre_topc(sK0,X1) = X1
% 3.39/0.93      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 3.39/0.93      | sK0 != sK0 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_431,c_377]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_494,plain,
% 3.39/0.93      ( ~ v3_pre_topc(X0,sK0)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_493]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_8,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.39/0.93      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.39/0.93      inference(cnf_transformation,[],[f53]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_506,plain,
% 3.39/0.93      ( ~ v3_pre_topc(X0,sK0)
% 3.39/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
% 3.39/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_494,c_8]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_22,negated_conjecture,
% 3.39/0.93      ( v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 3.39/0.93      inference(cnf_transformation,[],[f68]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_542,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.39/0.93      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 3.39/0.93      | sK3 != X0
% 3.39/0.93      | sK0 != sK0 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_506,c_22]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_543,plain,
% 3.39/0.93      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.39/0.93      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_542]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_545,plain,
% 3.39/0.93      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.39/0.93      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.39/0.93      inference(global_propositional_subsumption,
% 3.39/0.93                [status(thm)],
% 3.39/0.93                [c_543,c_23]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1152,plain,
% 3.39/0.93      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
% 3.39/0.93      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_2172,plain,
% 3.39/0.93      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.39/0.93      inference(global_propositional_subsumption,
% 3.39/0.93                [status(thm)],
% 3.39/0.93                [c_1152,c_24,c_545,c_1317,c_1323]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_12,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | ~ l1_pre_topc(X1)
% 3.39/0.93      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.39/0.93      inference(cnf_transformation,[],[f57]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_418,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/0.93      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 3.39/0.93      | sK0 != X1 ),
% 3.39/0.93      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_419,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/0.93      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.39/0.93      inference(unflattening,[status(thm)],[c_418]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1154,plain,
% 3.39/0.93      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.39/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_2012,plain,
% 3.39/0.93      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_1373,c_1154]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_2175,plain,
% 3.39/0.93      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
% 3.39/0.93      inference(demodulation,[status(thm)],[c_2172,c_2012]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_9,plain,
% 3.39/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.39/0.93      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.39/0.93      inference(cnf_transformation,[],[f54]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1162,plain,
% 3.39/0.93      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.39/0.93      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_2689,plain,
% 3.39/0.93      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_1373,c_1162]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_3102,plain,
% 3.39/0.93      ( k1_tops_1(sK0,sK3) = sK3 ),
% 3.39/0.93      inference(light_normalisation,[status(thm)],[c_2175,c_2689]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_5933,plain,
% 3.39/0.93      ( k2_xboole_0(sK3,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 3.39/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.39/0.93      | r1_tarski(sK3,X0) != iProver_top ),
% 3.39/0.93      inference(light_normalisation,[status(thm)],[c_5905,c_3102]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_8252,plain,
% 3.39/0.93      ( k2_xboole_0(sK3,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2)
% 3.39/0.93      | r1_tarski(sK3,sK2) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_1158,c_5933]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_21,negated_conjecture,
% 3.39/0.93      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(sK3,sK2) ),
% 3.39/0.93      inference(cnf_transformation,[],[f69]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_32,plain,
% 3.39/0.93      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.39/0.93      | r1_tarski(sK3,sK2) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_8298,plain,
% 3.39/0.93      ( k2_xboole_0(sK3,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 3.39/0.93      inference(global_propositional_subsumption,
% 3.39/0.93                [status(thm)],
% 3.39/0.93                [c_8252,c_29,c_32,c_1318,c_1324]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_20,negated_conjecture,
% 3.39/0.93      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r2_hidden(sK1,sK3) ),
% 3.39/0.93      inference(cnf_transformation,[],[f70]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1161,plain,
% 3.39/0.93      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.39/0.93      | r2_hidden(sK1,sK3) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_33,plain,
% 3.39/0.93      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.39/0.93      | r2_hidden(sK1,sK3) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1367,plain,
% 3.39/0.93      ( r2_hidden(sK1,sK3) = iProver_top ),
% 3.39/0.93      inference(global_propositional_subsumption,
% 3.39/0.93                [status(thm)],
% 3.39/0.93                [c_1161,c_29,c_33,c_1318,c_1324]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_5,plain,
% 3.39/0.93      ( ~ r2_hidden(X0,X1)
% 3.39/0.93      | ~ r2_hidden(X2,X1)
% 3.39/0.93      | r1_tarski(k2_tarski(X2,X0),X1) ),
% 3.39/0.93      inference(cnf_transformation,[],[f52]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1166,plain,
% 3.39/0.93      ( r2_hidden(X0,X1) != iProver_top
% 3.39/0.93      | r2_hidden(X2,X1) != iProver_top
% 3.39/0.93      | r1_tarski(k2_tarski(X2,X0),X1) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_3244,plain,
% 3.39/0.93      ( k2_xboole_0(k2_tarski(X0,X1),X2) = X2
% 3.39/0.93      | r2_hidden(X1,X2) != iProver_top
% 3.39/0.93      | r2_hidden(X0,X2) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_1166,c_1167]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_12763,plain,
% 3.39/0.93      ( k2_xboole_0(k2_tarski(sK1,X0),sK3) = sK3
% 3.39/0.93      | r2_hidden(X0,sK3) != iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_1367,c_3244]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_13279,plain,
% 3.39/0.93      ( k2_xboole_0(k2_tarski(sK1,sK1),sK3) = sK3 ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_1367,c_12763]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_2,plain,
% 3.39/0.93      ( r1_tarski(X0,X0) ),
% 3.39/0.93      inference(cnf_transformation,[],[f73]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1169,plain,
% 3.39/0.93      ( r1_tarski(X0,X0) = iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_3,plain,
% 3.39/0.93      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.39/0.93      inference(cnf_transformation,[],[f48]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1168,plain,
% 3.39/0.93      ( r1_tarski(X0,X1) = iProver_top
% 3.39/0.93      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_2301,plain,
% 3.39/0.93      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_1169,c_1168]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_4231,plain,
% 3.39/0.93      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_2301,c_1168]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_6,plain,
% 3.39/0.93      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_tarski(X2,X0),X1) ),
% 3.39/0.93      inference(cnf_transformation,[],[f51]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_1165,plain,
% 3.39/0.93      ( r2_hidden(X0,X1) = iProver_top
% 3.39/0.93      | r1_tarski(k2_tarski(X2,X0),X1) != iProver_top ),
% 3.39/0.93      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_4953,plain,
% 3.39/0.93      ( r2_hidden(X0,k2_xboole_0(k2_xboole_0(k2_tarski(X1,X0),X2),X3)) = iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_4231,c_1165]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_13327,plain,
% 3.39/0.93      ( r2_hidden(sK1,k2_xboole_0(sK3,X0)) = iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_13279,c_4953]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(c_13483,plain,
% 3.39/0.93      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.39/0.93      inference(superposition,[status(thm)],[c_8298,c_13327]) ).
% 3.39/0.93  
% 3.39/0.93  cnf(contradiction,plain,
% 3.39/0.93      ( $false ),
% 3.39/0.93      inference(minisat,[status(thm)],[c_13483,c_1324,c_1318,c_29]) ).
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/0.93  
% 3.39/0.93  ------                               Statistics
% 3.39/0.93  
% 3.39/0.93  ------ General
% 3.39/0.93  
% 3.39/0.93  abstr_ref_over_cycles:                  0
% 3.39/0.93  abstr_ref_under_cycles:                 0
% 3.39/0.93  gc_basic_clause_elim:                   0
% 3.39/0.93  forced_gc_time:                         0
% 3.39/0.93  parsing_time:                           0.008
% 3.39/0.93  unif_index_cands_time:                  0.
% 3.39/0.93  unif_index_add_time:                    0.
% 3.39/0.93  orderings_time:                         0.
% 3.39/0.93  out_proof_time:                         0.01
% 3.39/0.93  total_time:                             0.389
% 3.39/0.93  num_of_symbols:                         49
% 3.39/0.93  num_of_terms:                           13513
% 3.39/0.93  
% 3.39/0.93  ------ Preprocessing
% 3.39/0.93  
% 3.39/0.93  num_of_splits:                          0
% 3.39/0.93  num_of_split_atoms:                     0
% 3.39/0.93  num_of_reused_defs:                     0
% 3.39/0.93  num_eq_ax_congr_red:                    14
% 3.39/0.93  num_of_sem_filtered_clauses:            1
% 3.39/0.93  num_of_subtypes:                        0
% 3.39/0.93  monotx_restored_types:                  0
% 3.39/0.93  sat_num_of_epr_types:                   0
% 3.39/0.93  sat_num_of_non_cyclic_types:            0
% 3.39/0.93  sat_guarded_non_collapsed_types:        0
% 3.39/0.93  num_pure_diseq_elim:                    0
% 3.39/0.93  simp_replaced_by:                       0
% 3.39/0.93  res_preprocessed:                       110
% 3.39/0.93  prep_upred:                             0
% 3.39/0.93  prep_unflattend:                        15
% 3.39/0.93  smt_new_axioms:                         0
% 3.39/0.93  pred_elim_cands:                        3
% 3.39/0.93  pred_elim:                              4
% 3.39/0.93  pred_elim_cl:                           5
% 3.39/0.93  pred_elim_cycles:                       6
% 3.39/0.93  merged_defs:                            0
% 3.39/0.93  merged_defs_ncl:                        0
% 3.39/0.93  bin_hyper_res:                          0
% 3.39/0.93  prep_cycles:                            4
% 3.39/0.93  pred_elim_time:                         0.006
% 3.39/0.93  splitting_time:                         0.
% 3.39/0.93  sem_filter_time:                        0.
% 3.39/0.93  monotx_time:                            0.
% 3.39/0.93  subtype_inf_time:                       0.
% 3.39/0.93  
% 3.39/0.93  ------ Problem properties
% 3.39/0.93  
% 3.39/0.93  clauses:                                21
% 3.39/0.93  conjectures:                            4
% 3.39/0.93  epr:                                    2
% 3.39/0.93  horn:                                   17
% 3.39/0.93  ground:                                 5
% 3.39/0.93  unary:                                  2
% 3.39/0.93  binary:                                 14
% 3.39/0.93  lits:                                   49
% 3.39/0.93  lits_eq:                                7
% 3.39/0.93  fd_pure:                                0
% 3.39/0.93  fd_pseudo:                              0
% 3.39/0.93  fd_cond:                                0
% 3.39/0.93  fd_pseudo_cond:                         1
% 3.39/0.93  ac_symbols:                             0
% 3.39/0.93  
% 3.39/0.93  ------ Propositional Solver
% 3.39/0.93  
% 3.39/0.93  prop_solver_calls:                      29
% 3.39/0.93  prop_fast_solver_calls:                 940
% 3.39/0.93  smt_solver_calls:                       0
% 3.39/0.93  smt_fast_solver_calls:                  0
% 3.39/0.93  prop_num_of_clauses:                    5189
% 3.39/0.93  prop_preprocess_simplified:             10374
% 3.39/0.93  prop_fo_subsumed:                       29
% 3.39/0.93  prop_solver_time:                       0.
% 3.39/0.93  smt_solver_time:                        0.
% 3.39/0.93  smt_fast_solver_time:                   0.
% 3.39/0.93  prop_fast_solver_time:                  0.
% 3.39/0.93  prop_unsat_core_time:                   0.001
% 3.39/0.93  
% 3.39/0.93  ------ QBF
% 3.39/0.93  
% 3.39/0.93  qbf_q_res:                              0
% 3.39/0.93  qbf_num_tautologies:                    0
% 3.39/0.93  qbf_prep_cycles:                        0
% 3.39/0.93  
% 3.39/0.93  ------ BMC1
% 3.39/0.93  
% 3.39/0.93  bmc1_current_bound:                     -1
% 3.39/0.93  bmc1_last_solved_bound:                 -1
% 3.39/0.93  bmc1_unsat_core_size:                   -1
% 3.39/0.93  bmc1_unsat_core_parents_size:           -1
% 3.39/0.93  bmc1_merge_next_fun:                    0
% 3.39/0.93  bmc1_unsat_core_clauses_time:           0.
% 3.39/0.93  
% 3.39/0.93  ------ Instantiation
% 3.39/0.93  
% 3.39/0.93  inst_num_of_clauses:                    1553
% 3.39/0.93  inst_num_in_passive:                    476
% 3.39/0.93  inst_num_in_active:                     724
% 3.39/0.93  inst_num_in_unprocessed:                355
% 3.39/0.93  inst_num_of_loops:                      760
% 3.39/0.93  inst_num_of_learning_restarts:          0
% 3.39/0.93  inst_num_moves_active_passive:          35
% 3.39/0.93  inst_lit_activity:                      0
% 3.39/0.93  inst_lit_activity_moves:                1
% 3.39/0.93  inst_num_tautologies:                   0
% 3.39/0.93  inst_num_prop_implied:                  0
% 3.39/0.93  inst_num_existing_simplified:           0
% 3.39/0.93  inst_num_eq_res_simplified:             0
% 3.39/0.93  inst_num_child_elim:                    0
% 3.39/0.93  inst_num_of_dismatching_blockings:      592
% 3.39/0.93  inst_num_of_non_proper_insts:           1854
% 3.39/0.93  inst_num_of_duplicates:                 0
% 3.39/0.93  inst_inst_num_from_inst_to_res:         0
% 3.39/0.93  inst_dismatching_checking_time:         0.
% 3.39/0.93  
% 3.39/0.93  ------ Resolution
% 3.39/0.93  
% 3.39/0.93  res_num_of_clauses:                     0
% 3.39/0.93  res_num_in_passive:                     0
% 3.39/0.93  res_num_in_active:                      0
% 3.39/0.93  res_num_of_loops:                       114
% 3.39/0.93  res_forward_subset_subsumed:            24
% 3.39/0.93  res_backward_subset_subsumed:           4
% 3.39/0.93  res_forward_subsumed:                   0
% 3.39/0.93  res_backward_subsumed:                  0
% 3.39/0.93  res_forward_subsumption_resolution:     2
% 3.39/0.93  res_backward_subsumption_resolution:    0
% 3.39/0.93  res_clause_to_clause_subsumption:       2212
% 3.39/0.93  res_orphan_elimination:                 0
% 3.39/0.93  res_tautology_del:                      16
% 3.39/0.93  res_num_eq_res_simplified:              0
% 3.39/0.93  res_num_sel_changes:                    0
% 3.39/0.93  res_moves_from_active_to_pass:          0
% 3.39/0.93  
% 3.39/0.93  ------ Superposition
% 3.39/0.93  
% 3.39/0.93  sup_time_total:                         0.
% 3.39/0.93  sup_time_generating:                    0.
% 3.39/0.93  sup_time_sim_full:                      0.
% 3.39/0.93  sup_time_sim_immed:                     0.
% 3.39/0.93  
% 3.39/0.93  sup_num_of_clauses:                     446
% 3.39/0.93  sup_num_in_active:                      145
% 3.39/0.93  sup_num_in_passive:                     301
% 3.39/0.93  sup_num_of_loops:                       150
% 3.39/0.93  sup_fw_superposition:                   732
% 3.39/0.93  sup_bw_superposition:                   400
% 3.39/0.93  sup_immediate_simplified:               323
% 3.39/0.93  sup_given_eliminated:                   0
% 3.39/0.93  comparisons_done:                       0
% 3.39/0.93  comparisons_avoided:                    0
% 3.39/0.93  
% 3.39/0.93  ------ Simplifications
% 3.39/0.93  
% 3.39/0.93  
% 3.39/0.93  sim_fw_subset_subsumed:                 24
% 3.39/0.93  sim_bw_subset_subsumed:                 2
% 3.39/0.93  sim_fw_subsumed:                        35
% 3.39/0.93  sim_bw_subsumed:                        0
% 3.39/0.93  sim_fw_subsumption_res:                 0
% 3.39/0.93  sim_bw_subsumption_res:                 0
% 3.39/0.93  sim_tautology_del:                      20
% 3.39/0.93  sim_eq_tautology_del:                   95
% 3.39/0.93  sim_eq_res_simp:                        0
% 3.39/0.93  sim_fw_demodulated:                     85
% 3.39/0.93  sim_bw_demodulated:                     11
% 3.39/0.93  sim_light_normalised:                   212
% 3.39/0.93  sim_joinable_taut:                      0
% 3.39/0.93  sim_joinable_simp:                      0
% 3.39/0.93  sim_ac_normalised:                      0
% 3.39/0.93  sim_smt_subsumption:                    0
% 3.39/0.93  
%------------------------------------------------------------------------------
