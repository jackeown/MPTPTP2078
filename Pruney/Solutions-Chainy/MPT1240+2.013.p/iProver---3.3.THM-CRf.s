%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:00 EST 2020

% Result     : Theorem 14.66s
% Output     : CNFRefutation 14.66s
% Verified   : 
% Statistics : Number of formulae       :  168 (1606 expanded)
%              Number of clauses        :  101 ( 400 expanded)
%              Number of leaves         :   18 ( 394 expanded)
%              Depth                    :   31
%              Number of atoms          :  555 (13663 expanded)
%              Number of equality atoms :  131 ( 298 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f33])).

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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f42,f41,f40])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1396,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1404,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1401,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_494,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_495,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_15,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_440,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_441,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_555,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) = X1
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_495,c_441])).

cnf(c_556,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_607,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | sK3 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_556,c_21])).

cnf(c_608,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_610,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_22])).

cnf(c_1388,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_612,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_1453,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_1454,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1453])).

cnf(c_18,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(X0,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_364,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_365,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_24])).

cnf(c_370,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(X0,sK2)
    | k1_tops_1(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_370])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_471])).

cnf(c_1463,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_1464,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_2829,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1388,c_28,c_612,c_1454,c_1464])).

cnf(c_2830,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2829])).

cnf(c_2833,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK3),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_2830])).

cnf(c_1397,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1556,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1397,c_28,c_29,c_1454,c_1464])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1400,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1961,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_1400])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_213,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_263,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_213])).

cnf(c_1395,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_4060,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) = k4_xboole_0(u1_struct_0(sK0),sK3) ),
    inference(superposition,[status(thm)],[c_1961,c_1395])).

cnf(c_5697,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)) = k4_xboole_0(u1_struct_0(sK0),sK3)
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK3),u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2833,c_4060])).

cnf(c_5699,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)) = k4_xboole_0(u1_struct_0(sK0),sK3) ),
    inference(superposition,[status(thm)],[c_1404,c_5697])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_1390,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_2236,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_1556,c_1390])).

cnf(c_5016,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_4060,c_2236])).

cnf(c_6001,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_5699,c_5016])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_264,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_213])).

cnf(c_1394,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_3344,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1961,c_1394])).

cnf(c_5014,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_4060,c_3344])).

cnf(c_6002,plain,
    ( k1_tops_1(sK0,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_6001,c_5014])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_1393,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_45988,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6002,c_1393])).

cnf(c_47983,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_45988,c_28,c_29,c_1454,c_1464])).

cnf(c_47991,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1396,c_47983])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_48219,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47991,c_28,c_31,c_1454,c_1464])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1399,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_32,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1551,plain,
    ( r2_hidden(sK1,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1399,c_28,c_32,c_1454,c_1464])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1403,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1405,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2740,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1405])).

cnf(c_3395,plain,
    ( k2_xboole_0(k1_tarski(sK1),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1551,c_2740])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1406,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3609,plain,
    ( r1_tarski(k1_tarski(sK1),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_1406])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1402,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3970,plain,
    ( r2_hidden(sK1,X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3609,c_1402])).

cnf(c_48232,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48219,c_3970])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48232,c_1464,c_1454,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 14.66/2.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.66/2.53  
% 14.66/2.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.66/2.53  
% 14.66/2.53  ------  iProver source info
% 14.66/2.53  
% 14.66/2.53  git: date: 2020-06-30 10:37:57 +0100
% 14.66/2.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.66/2.53  git: non_committed_changes: false
% 14.66/2.53  git: last_make_outside_of_git: false
% 14.66/2.53  
% 14.66/2.53  ------ 
% 14.66/2.53  
% 14.66/2.53  ------ Input Options
% 14.66/2.53  
% 14.66/2.53  --out_options                           all
% 14.66/2.53  --tptp_safe_out                         true
% 14.66/2.53  --problem_path                          ""
% 14.66/2.53  --include_path                          ""
% 14.66/2.53  --clausifier                            res/vclausify_rel
% 14.66/2.53  --clausifier_options                    ""
% 14.66/2.53  --stdin                                 false
% 14.66/2.53  --stats_out                             all
% 14.66/2.53  
% 14.66/2.53  ------ General Options
% 14.66/2.53  
% 14.66/2.53  --fof                                   false
% 14.66/2.53  --time_out_real                         305.
% 14.66/2.53  --time_out_virtual                      -1.
% 14.66/2.53  --symbol_type_check                     false
% 14.66/2.53  --clausify_out                          false
% 14.66/2.53  --sig_cnt_out                           false
% 14.66/2.53  --trig_cnt_out                          false
% 14.66/2.53  --trig_cnt_out_tolerance                1.
% 14.66/2.53  --trig_cnt_out_sk_spl                   false
% 14.66/2.53  --abstr_cl_out                          false
% 14.66/2.53  
% 14.66/2.53  ------ Global Options
% 14.66/2.53  
% 14.66/2.53  --schedule                              default
% 14.66/2.53  --add_important_lit                     false
% 14.66/2.53  --prop_solver_per_cl                    1000
% 14.66/2.53  --min_unsat_core                        false
% 14.66/2.53  --soft_assumptions                      false
% 14.66/2.53  --soft_lemma_size                       3
% 14.66/2.53  --prop_impl_unit_size                   0
% 14.66/2.53  --prop_impl_unit                        []
% 14.66/2.53  --share_sel_clauses                     true
% 14.66/2.53  --reset_solvers                         false
% 14.66/2.53  --bc_imp_inh                            [conj_cone]
% 14.66/2.53  --conj_cone_tolerance                   3.
% 14.66/2.53  --extra_neg_conj                        none
% 14.66/2.53  --large_theory_mode                     true
% 14.66/2.53  --prolific_symb_bound                   200
% 14.66/2.53  --lt_threshold                          2000
% 14.66/2.53  --clause_weak_htbl                      true
% 14.66/2.53  --gc_record_bc_elim                     false
% 14.66/2.53  
% 14.66/2.53  ------ Preprocessing Options
% 14.66/2.53  
% 14.66/2.53  --preprocessing_flag                    true
% 14.66/2.53  --time_out_prep_mult                    0.1
% 14.66/2.53  --splitting_mode                        input
% 14.66/2.53  --splitting_grd                         true
% 14.66/2.53  --splitting_cvd                         false
% 14.66/2.53  --splitting_cvd_svl                     false
% 14.66/2.53  --splitting_nvd                         32
% 14.66/2.53  --sub_typing                            true
% 14.66/2.53  --prep_gs_sim                           true
% 14.66/2.53  --prep_unflatten                        true
% 14.66/2.53  --prep_res_sim                          true
% 14.66/2.53  --prep_upred                            true
% 14.66/2.53  --prep_sem_filter                       exhaustive
% 14.66/2.53  --prep_sem_filter_out                   false
% 14.66/2.53  --pred_elim                             true
% 14.66/2.53  --res_sim_input                         true
% 14.66/2.53  --eq_ax_congr_red                       true
% 14.66/2.53  --pure_diseq_elim                       true
% 14.66/2.53  --brand_transform                       false
% 14.66/2.53  --non_eq_to_eq                          false
% 14.66/2.53  --prep_def_merge                        true
% 14.66/2.53  --prep_def_merge_prop_impl              false
% 14.66/2.53  --prep_def_merge_mbd                    true
% 14.66/2.53  --prep_def_merge_tr_red                 false
% 14.66/2.53  --prep_def_merge_tr_cl                  false
% 14.66/2.53  --smt_preprocessing                     true
% 14.66/2.53  --smt_ac_axioms                         fast
% 14.66/2.53  --preprocessed_out                      false
% 14.66/2.53  --preprocessed_stats                    false
% 14.66/2.53  
% 14.66/2.53  ------ Abstraction refinement Options
% 14.66/2.53  
% 14.66/2.53  --abstr_ref                             []
% 14.66/2.53  --abstr_ref_prep                        false
% 14.66/2.53  --abstr_ref_until_sat                   false
% 14.66/2.53  --abstr_ref_sig_restrict                funpre
% 14.66/2.53  --abstr_ref_af_restrict_to_split_sk     false
% 14.66/2.53  --abstr_ref_under                       []
% 14.66/2.53  
% 14.66/2.53  ------ SAT Options
% 14.66/2.53  
% 14.66/2.53  --sat_mode                              false
% 14.66/2.53  --sat_fm_restart_options                ""
% 14.66/2.53  --sat_gr_def                            false
% 14.66/2.53  --sat_epr_types                         true
% 14.66/2.53  --sat_non_cyclic_types                  false
% 14.66/2.53  --sat_finite_models                     false
% 14.66/2.53  --sat_fm_lemmas                         false
% 14.66/2.53  --sat_fm_prep                           false
% 14.66/2.53  --sat_fm_uc_incr                        true
% 14.66/2.53  --sat_out_model                         small
% 14.66/2.53  --sat_out_clauses                       false
% 14.66/2.53  
% 14.66/2.53  ------ QBF Options
% 14.66/2.53  
% 14.66/2.53  --qbf_mode                              false
% 14.66/2.53  --qbf_elim_univ                         false
% 14.66/2.53  --qbf_dom_inst                          none
% 14.66/2.53  --qbf_dom_pre_inst                      false
% 14.66/2.53  --qbf_sk_in                             false
% 14.66/2.53  --qbf_pred_elim                         true
% 14.66/2.53  --qbf_split                             512
% 14.66/2.53  
% 14.66/2.53  ------ BMC1 Options
% 14.66/2.53  
% 14.66/2.53  --bmc1_incremental                      false
% 14.66/2.53  --bmc1_axioms                           reachable_all
% 14.66/2.53  --bmc1_min_bound                        0
% 14.66/2.53  --bmc1_max_bound                        -1
% 14.66/2.53  --bmc1_max_bound_default                -1
% 14.66/2.53  --bmc1_symbol_reachability              true
% 14.66/2.53  --bmc1_property_lemmas                  false
% 14.66/2.53  --bmc1_k_induction                      false
% 14.66/2.53  --bmc1_non_equiv_states                 false
% 14.66/2.53  --bmc1_deadlock                         false
% 14.66/2.53  --bmc1_ucm                              false
% 14.66/2.53  --bmc1_add_unsat_core                   none
% 14.66/2.53  --bmc1_unsat_core_children              false
% 14.66/2.53  --bmc1_unsat_core_extrapolate_axioms    false
% 14.66/2.53  --bmc1_out_stat                         full
% 14.66/2.53  --bmc1_ground_init                      false
% 14.66/2.53  --bmc1_pre_inst_next_state              false
% 14.66/2.53  --bmc1_pre_inst_state                   false
% 14.66/2.53  --bmc1_pre_inst_reach_state             false
% 14.66/2.53  --bmc1_out_unsat_core                   false
% 14.66/2.53  --bmc1_aig_witness_out                  false
% 14.66/2.53  --bmc1_verbose                          false
% 14.66/2.53  --bmc1_dump_clauses_tptp                false
% 14.66/2.53  --bmc1_dump_unsat_core_tptp             false
% 14.66/2.53  --bmc1_dump_file                        -
% 14.66/2.53  --bmc1_ucm_expand_uc_limit              128
% 14.66/2.53  --bmc1_ucm_n_expand_iterations          6
% 14.66/2.53  --bmc1_ucm_extend_mode                  1
% 14.66/2.53  --bmc1_ucm_init_mode                    2
% 14.66/2.53  --bmc1_ucm_cone_mode                    none
% 14.66/2.53  --bmc1_ucm_reduced_relation_type        0
% 14.66/2.53  --bmc1_ucm_relax_model                  4
% 14.66/2.53  --bmc1_ucm_full_tr_after_sat            true
% 14.66/2.53  --bmc1_ucm_expand_neg_assumptions       false
% 14.66/2.53  --bmc1_ucm_layered_model                none
% 14.66/2.53  --bmc1_ucm_max_lemma_size               10
% 14.66/2.53  
% 14.66/2.53  ------ AIG Options
% 14.66/2.53  
% 14.66/2.53  --aig_mode                              false
% 14.66/2.53  
% 14.66/2.53  ------ Instantiation Options
% 14.66/2.53  
% 14.66/2.53  --instantiation_flag                    true
% 14.66/2.53  --inst_sos_flag                         true
% 14.66/2.53  --inst_sos_phase                        true
% 14.66/2.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.66/2.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.66/2.53  --inst_lit_sel_side                     num_symb
% 14.66/2.53  --inst_solver_per_active                1400
% 14.66/2.53  --inst_solver_calls_frac                1.
% 14.66/2.53  --inst_passive_queue_type               priority_queues
% 14.66/2.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.66/2.53  --inst_passive_queues_freq              [25;2]
% 14.66/2.53  --inst_dismatching                      true
% 14.66/2.53  --inst_eager_unprocessed_to_passive     true
% 14.66/2.53  --inst_prop_sim_given                   true
% 14.66/2.53  --inst_prop_sim_new                     false
% 14.66/2.53  --inst_subs_new                         false
% 14.66/2.53  --inst_eq_res_simp                      false
% 14.66/2.53  --inst_subs_given                       false
% 14.66/2.53  --inst_orphan_elimination               true
% 14.66/2.53  --inst_learning_loop_flag               true
% 14.66/2.53  --inst_learning_start                   3000
% 14.66/2.53  --inst_learning_factor                  2
% 14.66/2.53  --inst_start_prop_sim_after_learn       3
% 14.66/2.53  --inst_sel_renew                        solver
% 14.66/2.53  --inst_lit_activity_flag                true
% 14.66/2.53  --inst_restr_to_given                   false
% 14.66/2.53  --inst_activity_threshold               500
% 14.66/2.53  --inst_out_proof                        true
% 14.66/2.53  
% 14.66/2.53  ------ Resolution Options
% 14.66/2.53  
% 14.66/2.53  --resolution_flag                       true
% 14.66/2.53  --res_lit_sel                           adaptive
% 14.66/2.53  --res_lit_sel_side                      none
% 14.66/2.53  --res_ordering                          kbo
% 14.66/2.53  --res_to_prop_solver                    active
% 14.66/2.53  --res_prop_simpl_new                    false
% 14.66/2.53  --res_prop_simpl_given                  true
% 14.66/2.53  --res_passive_queue_type                priority_queues
% 14.66/2.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.66/2.53  --res_passive_queues_freq               [15;5]
% 14.66/2.53  --res_forward_subs                      full
% 14.66/2.53  --res_backward_subs                     full
% 14.66/2.53  --res_forward_subs_resolution           true
% 14.66/2.53  --res_backward_subs_resolution          true
% 14.66/2.53  --res_orphan_elimination                true
% 14.66/2.53  --res_time_limit                        2.
% 14.66/2.53  --res_out_proof                         true
% 14.66/2.53  
% 14.66/2.53  ------ Superposition Options
% 14.66/2.53  
% 14.66/2.53  --superposition_flag                    true
% 14.66/2.53  --sup_passive_queue_type                priority_queues
% 14.66/2.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.66/2.53  --sup_passive_queues_freq               [8;1;4]
% 14.66/2.53  --demod_completeness_check              fast
% 14.66/2.53  --demod_use_ground                      true
% 14.66/2.53  --sup_to_prop_solver                    passive
% 14.66/2.53  --sup_prop_simpl_new                    true
% 14.66/2.53  --sup_prop_simpl_given                  true
% 14.66/2.53  --sup_fun_splitting                     true
% 14.66/2.53  --sup_smt_interval                      50000
% 14.66/2.53  
% 14.66/2.53  ------ Superposition Simplification Setup
% 14.66/2.53  
% 14.66/2.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 14.66/2.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 14.66/2.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 14.66/2.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 14.66/2.53  --sup_full_triv                         [TrivRules;PropSubs]
% 14.66/2.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 14.66/2.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 14.66/2.53  --sup_immed_triv                        [TrivRules]
% 14.66/2.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.66/2.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.66/2.53  --sup_immed_bw_main                     []
% 14.66/2.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 14.66/2.53  --sup_input_triv                        [Unflattening;TrivRules]
% 14.66/2.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.66/2.53  --sup_input_bw                          []
% 14.66/2.53  
% 14.66/2.53  ------ Combination Options
% 14.66/2.53  
% 14.66/2.53  --comb_res_mult                         3
% 14.66/2.53  --comb_sup_mult                         2
% 14.66/2.53  --comb_inst_mult                        10
% 14.66/2.53  
% 14.66/2.53  ------ Debug Options
% 14.66/2.53  
% 14.66/2.53  --dbg_backtrace                         false
% 14.66/2.53  --dbg_dump_prop_clauses                 false
% 14.66/2.53  --dbg_dump_prop_clauses_file            -
% 14.66/2.53  --dbg_out_stat                          false
% 14.66/2.53  ------ Parsing...
% 14.66/2.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.66/2.53  
% 14.66/2.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 14.66/2.53  
% 14.66/2.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.66/2.53  
% 14.66/2.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 14.66/2.53  ------ Proving...
% 14.66/2.53  ------ Problem Properties 
% 14.66/2.53  
% 14.66/2.53  
% 14.66/2.53  clauses                                 21
% 14.66/2.53  conjectures                             4
% 14.66/2.53  EPR                                     0
% 14.66/2.53  Horn                                    17
% 14.66/2.53  unary                                   2
% 14.66/2.53  binary                                  14
% 14.66/2.53  lits                                    50
% 14.66/2.53  lits eq                                 7
% 14.66/2.53  fd_pure                                 0
% 14.66/2.53  fd_pseudo                               0
% 14.66/2.53  fd_cond                                 0
% 14.66/2.53  fd_pseudo_cond                          0
% 14.66/2.53  AC symbols                              0
% 14.66/2.53  
% 14.66/2.53  ------ Schedule dynamic 5 is on 
% 14.66/2.53  
% 14.66/2.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 14.66/2.53  
% 14.66/2.53  
% 14.66/2.53  ------ 
% 14.66/2.53  Current options:
% 14.66/2.53  ------ 
% 14.66/2.53  
% 14.66/2.53  ------ Input Options
% 14.66/2.53  
% 14.66/2.53  --out_options                           all
% 14.66/2.53  --tptp_safe_out                         true
% 14.66/2.53  --problem_path                          ""
% 14.66/2.53  --include_path                          ""
% 14.66/2.53  --clausifier                            res/vclausify_rel
% 14.66/2.53  --clausifier_options                    ""
% 14.66/2.53  --stdin                                 false
% 14.66/2.53  --stats_out                             all
% 14.66/2.53  
% 14.66/2.53  ------ General Options
% 14.66/2.53  
% 14.66/2.53  --fof                                   false
% 14.66/2.53  --time_out_real                         305.
% 14.66/2.53  --time_out_virtual                      -1.
% 14.66/2.53  --symbol_type_check                     false
% 14.66/2.53  --clausify_out                          false
% 14.66/2.53  --sig_cnt_out                           false
% 14.66/2.53  --trig_cnt_out                          false
% 14.66/2.53  --trig_cnt_out_tolerance                1.
% 14.66/2.53  --trig_cnt_out_sk_spl                   false
% 14.66/2.53  --abstr_cl_out                          false
% 14.66/2.53  
% 14.66/2.53  ------ Global Options
% 14.66/2.53  
% 14.66/2.53  --schedule                              default
% 14.66/2.53  --add_important_lit                     false
% 14.66/2.53  --prop_solver_per_cl                    1000
% 14.66/2.53  --min_unsat_core                        false
% 14.66/2.53  --soft_assumptions                      false
% 14.66/2.53  --soft_lemma_size                       3
% 14.66/2.53  --prop_impl_unit_size                   0
% 14.66/2.53  --prop_impl_unit                        []
% 14.66/2.53  --share_sel_clauses                     true
% 14.66/2.53  --reset_solvers                         false
% 14.66/2.53  --bc_imp_inh                            [conj_cone]
% 14.66/2.53  --conj_cone_tolerance                   3.
% 14.66/2.53  --extra_neg_conj                        none
% 14.66/2.53  --large_theory_mode                     true
% 14.66/2.53  --prolific_symb_bound                   200
% 14.66/2.53  --lt_threshold                          2000
% 14.66/2.53  --clause_weak_htbl                      true
% 14.66/2.53  --gc_record_bc_elim                     false
% 14.66/2.53  
% 14.66/2.53  ------ Preprocessing Options
% 14.66/2.53  
% 14.66/2.53  --preprocessing_flag                    true
% 14.66/2.53  --time_out_prep_mult                    0.1
% 14.66/2.53  --splitting_mode                        input
% 14.66/2.53  --splitting_grd                         true
% 14.66/2.53  --splitting_cvd                         false
% 14.66/2.53  --splitting_cvd_svl                     false
% 14.66/2.53  --splitting_nvd                         32
% 14.66/2.53  --sub_typing                            true
% 14.66/2.53  --prep_gs_sim                           true
% 14.66/2.53  --prep_unflatten                        true
% 14.66/2.53  --prep_res_sim                          true
% 14.66/2.53  --prep_upred                            true
% 14.66/2.53  --prep_sem_filter                       exhaustive
% 14.66/2.53  --prep_sem_filter_out                   false
% 14.66/2.53  --pred_elim                             true
% 14.66/2.53  --res_sim_input                         true
% 14.66/2.53  --eq_ax_congr_red                       true
% 14.66/2.53  --pure_diseq_elim                       true
% 14.66/2.53  --brand_transform                       false
% 14.66/2.53  --non_eq_to_eq                          false
% 14.66/2.53  --prep_def_merge                        true
% 14.66/2.53  --prep_def_merge_prop_impl              false
% 14.66/2.53  --prep_def_merge_mbd                    true
% 14.66/2.53  --prep_def_merge_tr_red                 false
% 14.66/2.53  --prep_def_merge_tr_cl                  false
% 14.66/2.53  --smt_preprocessing                     true
% 14.66/2.53  --smt_ac_axioms                         fast
% 14.66/2.53  --preprocessed_out                      false
% 14.66/2.53  --preprocessed_stats                    false
% 14.66/2.53  
% 14.66/2.53  ------ Abstraction refinement Options
% 14.66/2.53  
% 14.66/2.53  --abstr_ref                             []
% 14.66/2.53  --abstr_ref_prep                        false
% 14.66/2.53  --abstr_ref_until_sat                   false
% 14.66/2.53  --abstr_ref_sig_restrict                funpre
% 14.66/2.53  --abstr_ref_af_restrict_to_split_sk     false
% 14.66/2.53  --abstr_ref_under                       []
% 14.66/2.53  
% 14.66/2.53  ------ SAT Options
% 14.66/2.53  
% 14.66/2.53  --sat_mode                              false
% 14.66/2.53  --sat_fm_restart_options                ""
% 14.66/2.53  --sat_gr_def                            false
% 14.66/2.53  --sat_epr_types                         true
% 14.66/2.53  --sat_non_cyclic_types                  false
% 14.66/2.53  --sat_finite_models                     false
% 14.66/2.53  --sat_fm_lemmas                         false
% 14.66/2.53  --sat_fm_prep                           false
% 14.66/2.53  --sat_fm_uc_incr                        true
% 14.66/2.53  --sat_out_model                         small
% 14.66/2.53  --sat_out_clauses                       false
% 14.66/2.53  
% 14.66/2.53  ------ QBF Options
% 14.66/2.53  
% 14.66/2.53  --qbf_mode                              false
% 14.66/2.53  --qbf_elim_univ                         false
% 14.66/2.53  --qbf_dom_inst                          none
% 14.66/2.53  --qbf_dom_pre_inst                      false
% 14.66/2.53  --qbf_sk_in                             false
% 14.66/2.53  --qbf_pred_elim                         true
% 14.66/2.53  --qbf_split                             512
% 14.66/2.53  
% 14.66/2.53  ------ BMC1 Options
% 14.66/2.53  
% 14.66/2.53  --bmc1_incremental                      false
% 14.66/2.53  --bmc1_axioms                           reachable_all
% 14.66/2.53  --bmc1_min_bound                        0
% 14.66/2.53  --bmc1_max_bound                        -1
% 14.66/2.53  --bmc1_max_bound_default                -1
% 14.66/2.53  --bmc1_symbol_reachability              true
% 14.66/2.53  --bmc1_property_lemmas                  false
% 14.66/2.53  --bmc1_k_induction                      false
% 14.66/2.53  --bmc1_non_equiv_states                 false
% 14.66/2.53  --bmc1_deadlock                         false
% 14.66/2.53  --bmc1_ucm                              false
% 14.66/2.53  --bmc1_add_unsat_core                   none
% 14.66/2.53  --bmc1_unsat_core_children              false
% 14.66/2.53  --bmc1_unsat_core_extrapolate_axioms    false
% 14.66/2.53  --bmc1_out_stat                         full
% 14.66/2.53  --bmc1_ground_init                      false
% 14.66/2.53  --bmc1_pre_inst_next_state              false
% 14.66/2.53  --bmc1_pre_inst_state                   false
% 14.66/2.53  --bmc1_pre_inst_reach_state             false
% 14.66/2.53  --bmc1_out_unsat_core                   false
% 14.66/2.53  --bmc1_aig_witness_out                  false
% 14.66/2.53  --bmc1_verbose                          false
% 14.66/2.53  --bmc1_dump_clauses_tptp                false
% 14.66/2.53  --bmc1_dump_unsat_core_tptp             false
% 14.66/2.53  --bmc1_dump_file                        -
% 14.66/2.53  --bmc1_ucm_expand_uc_limit              128
% 14.66/2.53  --bmc1_ucm_n_expand_iterations          6
% 14.66/2.53  --bmc1_ucm_extend_mode                  1
% 14.66/2.53  --bmc1_ucm_init_mode                    2
% 14.66/2.53  --bmc1_ucm_cone_mode                    none
% 14.66/2.53  --bmc1_ucm_reduced_relation_type        0
% 14.66/2.53  --bmc1_ucm_relax_model                  4
% 14.66/2.53  --bmc1_ucm_full_tr_after_sat            true
% 14.66/2.53  --bmc1_ucm_expand_neg_assumptions       false
% 14.66/2.53  --bmc1_ucm_layered_model                none
% 14.66/2.53  --bmc1_ucm_max_lemma_size               10
% 14.66/2.53  
% 14.66/2.53  ------ AIG Options
% 14.66/2.53  
% 14.66/2.53  --aig_mode                              false
% 14.66/2.53  
% 14.66/2.53  ------ Instantiation Options
% 14.66/2.53  
% 14.66/2.53  --instantiation_flag                    true
% 14.66/2.53  --inst_sos_flag                         true
% 14.66/2.53  --inst_sos_phase                        true
% 14.66/2.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.66/2.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.66/2.53  --inst_lit_sel_side                     none
% 14.66/2.53  --inst_solver_per_active                1400
% 14.66/2.53  --inst_solver_calls_frac                1.
% 14.66/2.53  --inst_passive_queue_type               priority_queues
% 14.66/2.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.66/2.53  --inst_passive_queues_freq              [25;2]
% 14.66/2.53  --inst_dismatching                      true
% 14.66/2.53  --inst_eager_unprocessed_to_passive     true
% 14.66/2.53  --inst_prop_sim_given                   true
% 14.66/2.53  --inst_prop_sim_new                     false
% 14.66/2.53  --inst_subs_new                         false
% 14.66/2.53  --inst_eq_res_simp                      false
% 14.66/2.53  --inst_subs_given                       false
% 14.66/2.53  --inst_orphan_elimination               true
% 14.66/2.53  --inst_learning_loop_flag               true
% 14.66/2.53  --inst_learning_start                   3000
% 14.66/2.53  --inst_learning_factor                  2
% 14.66/2.53  --inst_start_prop_sim_after_learn       3
% 14.66/2.53  --inst_sel_renew                        solver
% 14.66/2.53  --inst_lit_activity_flag                true
% 14.66/2.53  --inst_restr_to_given                   false
% 14.66/2.53  --inst_activity_threshold               500
% 14.66/2.53  --inst_out_proof                        true
% 14.66/2.53  
% 14.66/2.53  ------ Resolution Options
% 14.66/2.53  
% 14.66/2.53  --resolution_flag                       false
% 14.66/2.53  --res_lit_sel                           adaptive
% 14.66/2.53  --res_lit_sel_side                      none
% 14.66/2.53  --res_ordering                          kbo
% 14.66/2.53  --res_to_prop_solver                    active
% 14.66/2.53  --res_prop_simpl_new                    false
% 14.66/2.53  --res_prop_simpl_given                  true
% 14.66/2.53  --res_passive_queue_type                priority_queues
% 14.66/2.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.66/2.53  --res_passive_queues_freq               [15;5]
% 14.66/2.53  --res_forward_subs                      full
% 14.66/2.53  --res_backward_subs                     full
% 14.66/2.53  --res_forward_subs_resolution           true
% 14.66/2.53  --res_backward_subs_resolution          true
% 14.66/2.53  --res_orphan_elimination                true
% 14.66/2.53  --res_time_limit                        2.
% 14.66/2.53  --res_out_proof                         true
% 14.66/2.53  
% 14.66/2.53  ------ Superposition Options
% 14.66/2.53  
% 14.66/2.53  --superposition_flag                    true
% 14.66/2.53  --sup_passive_queue_type                priority_queues
% 14.66/2.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.66/2.53  --sup_passive_queues_freq               [8;1;4]
% 14.66/2.53  --demod_completeness_check              fast
% 14.66/2.53  --demod_use_ground                      true
% 14.66/2.53  --sup_to_prop_solver                    passive
% 14.66/2.53  --sup_prop_simpl_new                    true
% 14.66/2.53  --sup_prop_simpl_given                  true
% 14.66/2.53  --sup_fun_splitting                     true
% 14.66/2.53  --sup_smt_interval                      50000
% 14.66/2.53  
% 14.66/2.53  ------ Superposition Simplification Setup
% 14.66/2.53  
% 14.66/2.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 14.66/2.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 14.66/2.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 14.66/2.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 14.66/2.53  --sup_full_triv                         [TrivRules;PropSubs]
% 14.66/2.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 14.66/2.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 14.66/2.53  --sup_immed_triv                        [TrivRules]
% 14.66/2.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.66/2.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.66/2.53  --sup_immed_bw_main                     []
% 14.66/2.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 14.66/2.53  --sup_input_triv                        [Unflattening;TrivRules]
% 14.66/2.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.66/2.53  --sup_input_bw                          []
% 14.66/2.53  
% 14.66/2.53  ------ Combination Options
% 14.66/2.53  
% 14.66/2.53  --comb_res_mult                         3
% 14.66/2.53  --comb_sup_mult                         2
% 14.66/2.53  --comb_inst_mult                        10
% 14.66/2.53  
% 14.66/2.53  ------ Debug Options
% 14.66/2.53  
% 14.66/2.53  --dbg_backtrace                         false
% 14.66/2.53  --dbg_dump_prop_clauses                 false
% 14.66/2.53  --dbg_dump_prop_clauses_file            -
% 14.66/2.53  --dbg_out_stat                          false
% 14.66/2.53  
% 14.66/2.53  
% 14.66/2.53  
% 14.66/2.53  
% 14.66/2.53  ------ Proving...
% 14.66/2.53  
% 14.66/2.53  
% 14.66/2.53  % SZS status Theorem for theBenchmark.p
% 14.66/2.53  
% 14.66/2.53  % SZS output start CNFRefutation for theBenchmark.p
% 14.66/2.53  
% 14.66/2.53  fof(f15,conjecture,(
% 14.66/2.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f16,negated_conjecture,(
% 14.66/2.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 14.66/2.53    inference(negated_conjecture,[],[f15])).
% 14.66/2.53  
% 14.66/2.53  fof(f32,plain,(
% 14.66/2.53    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 14.66/2.53    inference(ennf_transformation,[],[f16])).
% 14.66/2.53  
% 14.66/2.53  fof(f33,plain,(
% 14.66/2.53    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 14.66/2.53    inference(flattening,[],[f32])).
% 14.66/2.53  
% 14.66/2.53  fof(f37,plain,(
% 14.66/2.53    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 14.66/2.53    inference(nnf_transformation,[],[f33])).
% 14.66/2.53  
% 14.66/2.53  fof(f38,plain,(
% 14.66/2.53    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 14.66/2.53    inference(flattening,[],[f37])).
% 14.66/2.53  
% 14.66/2.53  fof(f39,plain,(
% 14.66/2.53    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 14.66/2.53    inference(rectify,[],[f38])).
% 14.66/2.53  
% 14.66/2.53  fof(f42,plain,(
% 14.66/2.53    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3) & r1_tarski(sK3,X2) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 14.66/2.53    introduced(choice_axiom,[])).
% 14.66/2.53  
% 14.66/2.53  fof(f41,plain,(
% 14.66/2.53    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK1,k1_tops_1(X0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK1,k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 14.66/2.53    introduced(choice_axiom,[])).
% 14.66/2.53  
% 14.66/2.53  fof(f40,plain,(
% 14.66/2.53    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 14.66/2.53    introduced(choice_axiom,[])).
% 14.66/2.53  
% 14.66/2.53  fof(f43,plain,(
% 14.66/2.53    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 14.66/2.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f42,f41,f40])).
% 14.66/2.53  
% 14.66/2.53  fof(f64,plain,(
% 14.66/2.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.66/2.53    inference(cnf_transformation,[],[f43])).
% 14.66/2.53  
% 14.66/2.53  fof(f3,axiom,(
% 14.66/2.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f46,plain,(
% 14.66/2.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f3])).
% 14.66/2.53  
% 14.66/2.53  fof(f7,axiom,(
% 14.66/2.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f35,plain,(
% 14.66/2.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 14.66/2.53    inference(nnf_transformation,[],[f7])).
% 14.66/2.53  
% 14.66/2.53  fof(f52,plain,(
% 14.66/2.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f35])).
% 14.66/2.53  
% 14.66/2.53  fof(f8,axiom,(
% 14.66/2.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f21,plain,(
% 14.66/2.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.66/2.53    inference(ennf_transformation,[],[f8])).
% 14.66/2.53  
% 14.66/2.53  fof(f22,plain,(
% 14.66/2.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.66/2.53    inference(flattening,[],[f21])).
% 14.66/2.53  
% 14.66/2.53  fof(f53,plain,(
% 14.66/2.53    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f22])).
% 14.66/2.53  
% 14.66/2.53  fof(f63,plain,(
% 14.66/2.53    l1_pre_topc(sK0)),
% 14.66/2.53    inference(cnf_transformation,[],[f43])).
% 14.66/2.53  
% 14.66/2.53  fof(f12,axiom,(
% 14.66/2.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f28,plain,(
% 14.66/2.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.66/2.53    inference(ennf_transformation,[],[f12])).
% 14.66/2.53  
% 14.66/2.53  fof(f36,plain,(
% 14.66/2.53    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.66/2.53    inference(nnf_transformation,[],[f28])).
% 14.66/2.53  
% 14.66/2.53  fof(f58,plain,(
% 14.66/2.53    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f36])).
% 14.66/2.53  
% 14.66/2.53  fof(f66,plain,(
% 14.66/2.53    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 14.66/2.53    inference(cnf_transformation,[],[f43])).
% 14.66/2.53  
% 14.66/2.53  fof(f65,plain,(
% 14.66/2.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 14.66/2.53    inference(cnf_transformation,[],[f43])).
% 14.66/2.53  
% 14.66/2.53  fof(f13,axiom,(
% 14.66/2.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f29,plain,(
% 14.66/2.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.66/2.53    inference(ennf_transformation,[],[f13])).
% 14.66/2.53  
% 14.66/2.53  fof(f60,plain,(
% 14.66/2.53    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f29])).
% 14.66/2.53  
% 14.66/2.53  fof(f69,plain,(
% 14.66/2.53    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 14.66/2.53    inference(cnf_transformation,[],[f43])).
% 14.66/2.53  
% 14.66/2.53  fof(f11,axiom,(
% 14.66/2.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f26,plain,(
% 14.66/2.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 14.66/2.53    inference(ennf_transformation,[],[f11])).
% 14.66/2.53  
% 14.66/2.53  fof(f27,plain,(
% 14.66/2.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 14.66/2.53    inference(flattening,[],[f26])).
% 14.66/2.53  
% 14.66/2.53  fof(f57,plain,(
% 14.66/2.53    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f27])).
% 14.66/2.53  
% 14.66/2.53  fof(f62,plain,(
% 14.66/2.53    v2_pre_topc(sK0)),
% 14.66/2.53    inference(cnf_transformation,[],[f43])).
% 14.66/2.53  
% 14.66/2.53  fof(f10,axiom,(
% 14.66/2.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f24,plain,(
% 14.66/2.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 14.66/2.53    inference(ennf_transformation,[],[f10])).
% 14.66/2.53  
% 14.66/2.53  fof(f25,plain,(
% 14.66/2.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 14.66/2.53    inference(flattening,[],[f24])).
% 14.66/2.53  
% 14.66/2.53  fof(f56,plain,(
% 14.66/2.53    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f25])).
% 14.66/2.53  
% 14.66/2.53  fof(f51,plain,(
% 14.66/2.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 14.66/2.53    inference(cnf_transformation,[],[f35])).
% 14.66/2.53  
% 14.66/2.53  fof(f5,axiom,(
% 14.66/2.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f19,plain,(
% 14.66/2.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 14.66/2.53    inference(ennf_transformation,[],[f5])).
% 14.66/2.53  
% 14.66/2.53  fof(f49,plain,(
% 14.66/2.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 14.66/2.53    inference(cnf_transformation,[],[f19])).
% 14.66/2.53  
% 14.66/2.53  fof(f9,axiom,(
% 14.66/2.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f23,plain,(
% 14.66/2.53    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.66/2.53    inference(ennf_transformation,[],[f9])).
% 14.66/2.53  
% 14.66/2.53  fof(f55,plain,(
% 14.66/2.53    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f23])).
% 14.66/2.53  
% 14.66/2.53  fof(f6,axiom,(
% 14.66/2.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f20,plain,(
% 14.66/2.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 14.66/2.53    inference(ennf_transformation,[],[f6])).
% 14.66/2.53  
% 14.66/2.53  fof(f50,plain,(
% 14.66/2.53    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 14.66/2.53    inference(cnf_transformation,[],[f20])).
% 14.66/2.53  
% 14.66/2.53  fof(f14,axiom,(
% 14.66/2.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f30,plain,(
% 14.66/2.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.66/2.53    inference(ennf_transformation,[],[f14])).
% 14.66/2.53  
% 14.66/2.53  fof(f31,plain,(
% 14.66/2.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.66/2.53    inference(flattening,[],[f30])).
% 14.66/2.53  
% 14.66/2.53  fof(f61,plain,(
% 14.66/2.53    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f31])).
% 14.66/2.53  
% 14.66/2.53  fof(f67,plain,(
% 14.66/2.53    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 14.66/2.53    inference(cnf_transformation,[],[f43])).
% 14.66/2.53  
% 14.66/2.53  fof(f68,plain,(
% 14.66/2.53    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 14.66/2.53    inference(cnf_transformation,[],[f43])).
% 14.66/2.53  
% 14.66/2.53  fof(f4,axiom,(
% 14.66/2.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f34,plain,(
% 14.66/2.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 14.66/2.53    inference(nnf_transformation,[],[f4])).
% 14.66/2.53  
% 14.66/2.53  fof(f48,plain,(
% 14.66/2.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f34])).
% 14.66/2.53  
% 14.66/2.53  fof(f2,axiom,(
% 14.66/2.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f18,plain,(
% 14.66/2.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 14.66/2.53    inference(ennf_transformation,[],[f2])).
% 14.66/2.53  
% 14.66/2.53  fof(f45,plain,(
% 14.66/2.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f18])).
% 14.66/2.53  
% 14.66/2.53  fof(f1,axiom,(
% 14.66/2.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 14.66/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.66/2.53  
% 14.66/2.53  fof(f17,plain,(
% 14.66/2.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 14.66/2.53    inference(ennf_transformation,[],[f1])).
% 14.66/2.53  
% 14.66/2.53  fof(f44,plain,(
% 14.66/2.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f17])).
% 14.66/2.53  
% 14.66/2.53  fof(f47,plain,(
% 14.66/2.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 14.66/2.53    inference(cnf_transformation,[],[f34])).
% 14.66/2.53  
% 14.66/2.53  cnf(c_23,negated_conjecture,
% 14.66/2.53      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 14.66/2.53      inference(cnf_transformation,[],[f64]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1396,plain,
% 14.66/2.53      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_2,plain,
% 14.66/2.53      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 14.66/2.53      inference(cnf_transformation,[],[f46]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1404,plain,
% 14.66/2.53      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_7,plain,
% 14.66/2.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 14.66/2.53      inference(cnf_transformation,[],[f52]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1401,plain,
% 14.66/2.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 14.66/2.53      | r1_tarski(X0,X1) != iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_10,plain,
% 14.66/2.53      ( ~ v4_pre_topc(X0,X1)
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | ~ l1_pre_topc(X1)
% 14.66/2.53      | k2_pre_topc(X1,X0) = X0 ),
% 14.66/2.53      inference(cnf_transformation,[],[f53]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_24,negated_conjecture,
% 14.66/2.53      ( l1_pre_topc(sK0) ),
% 14.66/2.53      inference(cnf_transformation,[],[f63]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_494,plain,
% 14.66/2.53      ( ~ v4_pre_topc(X0,X1)
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | k2_pre_topc(X1,X0) = X0
% 14.66/2.53      | sK0 != X1 ),
% 14.66/2.53      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_495,plain,
% 14.66/2.53      ( ~ v4_pre_topc(X0,sK0)
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | k2_pre_topc(sK0,X0) = X0 ),
% 14.66/2.53      inference(unflattening,[status(thm)],[c_494]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_15,plain,
% 14.66/2.53      ( ~ v3_pre_topc(X0,X1)
% 14.66/2.53      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | ~ l1_pre_topc(X1) ),
% 14.66/2.53      inference(cnf_transformation,[],[f58]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_440,plain,
% 14.66/2.53      ( ~ v3_pre_topc(X0,X1)
% 14.66/2.53      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | sK0 != X1 ),
% 14.66/2.53      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_441,plain,
% 14.66/2.53      ( ~ v3_pre_topc(X0,sK0)
% 14.66/2.53      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 14.66/2.53      inference(unflattening,[status(thm)],[c_440]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_555,plain,
% 14.66/2.53      ( ~ v3_pre_topc(X0,sK0)
% 14.66/2.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | k2_pre_topc(sK0,X1) = X1
% 14.66/2.53      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 14.66/2.53      | sK0 != sK0 ),
% 14.66/2.53      inference(resolution_lifted,[status(thm)],[c_495,c_441]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_556,plain,
% 14.66/2.53      ( ~ v3_pre_topc(X0,sK0)
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
% 14.66/2.53      inference(unflattening,[status(thm)],[c_555]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_21,negated_conjecture,
% 14.66/2.53      ( v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 14.66/2.53      inference(cnf_transformation,[],[f66]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_607,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 14.66/2.53      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 14.66/2.53      | sK3 != X0
% 14.66/2.53      | sK0 != sK0 ),
% 14.66/2.53      inference(resolution_lifted,[status(thm)],[c_556,c_21]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_608,plain,
% 14.66/2.53      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 14.66/2.53      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 14.66/2.53      inference(unflattening,[status(thm)],[c_607]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_22,negated_conjecture,
% 14.66/2.53      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 14.66/2.53      inference(cnf_transformation,[],[f65]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_610,plain,
% 14.66/2.53      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 14.66/2.53      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 14.66/2.53      inference(global_propositional_subsumption,
% 14.66/2.53                [status(thm)],
% 14.66/2.53                [c_608,c_22]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1388,plain,
% 14.66/2.53      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
% 14.66/2.53      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.66/2.53      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_28,plain,
% 14.66/2.53      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_612,plain,
% 14.66/2.53      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
% 14.66/2.53      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.66/2.53      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_16,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | r1_tarski(k1_tops_1(X1,X0),X0)
% 14.66/2.53      | ~ l1_pre_topc(X1) ),
% 14.66/2.53      inference(cnf_transformation,[],[f60]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_428,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | r1_tarski(k1_tops_1(X1,X0),X0)
% 14.66/2.53      | sK0 != X1 ),
% 14.66/2.53      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_429,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 14.66/2.53      inference(unflattening,[status(thm)],[c_428]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1453,plain,
% 14.66/2.53      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 14.66/2.53      inference(instantiation,[status(thm)],[c_429]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1454,plain,
% 14.66/2.53      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.66/2.53      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_1453]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_18,negated_conjecture,
% 14.66/2.53      ( ~ v3_pre_topc(X0,sK0)
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ r2_hidden(sK1,X0)
% 14.66/2.53      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 14.66/2.53      | ~ r1_tarski(X0,sK2) ),
% 14.66/2.53      inference(cnf_transformation,[],[f69]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_13,plain,
% 14.66/2.53      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 14.66/2.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 14.66/2.53      | ~ l1_pre_topc(X0)
% 14.66/2.53      | ~ v2_pre_topc(X0) ),
% 14.66/2.53      inference(cnf_transformation,[],[f57]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_25,negated_conjecture,
% 14.66/2.53      ( v2_pre_topc(sK0) ),
% 14.66/2.53      inference(cnf_transformation,[],[f62]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_364,plain,
% 14.66/2.53      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 14.66/2.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 14.66/2.53      | ~ l1_pre_topc(X0)
% 14.66/2.53      | sK0 != X0 ),
% 14.66/2.53      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_365,plain,
% 14.66/2.53      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ l1_pre_topc(sK0) ),
% 14.66/2.53      inference(unflattening,[status(thm)],[c_364]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_369,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 14.66/2.53      inference(global_propositional_subsumption,
% 14.66/2.53                [status(thm)],
% 14.66/2.53                [c_365,c_24]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_370,plain,
% 14.66/2.53      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 14.66/2.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 14.66/2.53      inference(renaming,[status(thm)],[c_369]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_647,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ r2_hidden(sK1,X0)
% 14.66/2.53      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 14.66/2.53      | ~ r1_tarski(X0,sK2)
% 14.66/2.53      | k1_tops_1(sK0,X1) != X0
% 14.66/2.53      | sK0 != sK0 ),
% 14.66/2.53      inference(resolution_lifted,[status(thm)],[c_18,c_370]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_648,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 14.66/2.53      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 14.66/2.53      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 14.66/2.53      inference(unflattening,[status(thm)],[c_647]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_12,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | ~ l1_pre_topc(X1) ),
% 14.66/2.53      inference(cnf_transformation,[],[f56]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_470,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | sK0 != X1 ),
% 14.66/2.53      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_471,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 14.66/2.53      inference(unflattening,[status(thm)],[c_470]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_652,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 14.66/2.53      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 14.66/2.53      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 14.66/2.53      inference(global_propositional_subsumption,
% 14.66/2.53                [status(thm)],
% 14.66/2.53                [c_648,c_471]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1463,plain,
% 14.66/2.53      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 14.66/2.53      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 14.66/2.53      inference(instantiation,[status(thm)],[c_652]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1464,plain,
% 14.66/2.53      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.66/2.53      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 14.66/2.53      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_2829,plain,
% 14.66/2.53      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.66/2.53      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 14.66/2.53      inference(global_propositional_subsumption,
% 14.66/2.53                [status(thm)],
% 14.66/2.53                [c_1388,c_28,c_612,c_1454,c_1464]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_2830,plain,
% 14.66/2.53      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
% 14.66/2.53      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 14.66/2.53      inference(renaming,[status(thm)],[c_2829]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_2833,plain,
% 14.66/2.53      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
% 14.66/2.53      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK3),u1_struct_0(sK0)) != iProver_top ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_1401,c_2830]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1397,plain,
% 14.66/2.53      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 14.66/2.53      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_29,plain,
% 14.66/2.53      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 14.66/2.53      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1556,plain,
% 14.66/2.53      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 14.66/2.53      inference(global_propositional_subsumption,
% 14.66/2.53                [status(thm)],
% 14.66/2.53                [c_1397,c_28,c_29,c_1454,c_1464]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_8,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 14.66/2.53      inference(cnf_transformation,[],[f51]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1400,plain,
% 14.66/2.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 14.66/2.53      | r1_tarski(X0,X1) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1961,plain,
% 14.66/2.53      ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_1556,c_1400]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_5,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 14.66/2.53      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 14.66/2.53      inference(cnf_transformation,[],[f49]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_212,plain,
% 14.66/2.53      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 14.66/2.53      inference(prop_impl,[status(thm)],[c_7]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_213,plain,
% 14.66/2.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 14.66/2.53      inference(renaming,[status(thm)],[c_212]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_263,plain,
% 14.66/2.53      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 14.66/2.53      inference(bin_hyper_res,[status(thm)],[c_5,c_213]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1395,plain,
% 14.66/2.53      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 14.66/2.53      | r1_tarski(X1,X0) != iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_4060,plain,
% 14.66/2.53      ( k3_subset_1(u1_struct_0(sK0),sK3) = k4_xboole_0(u1_struct_0(sK0),sK3) ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_1961,c_1395]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_5697,plain,
% 14.66/2.53      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)) = k4_xboole_0(u1_struct_0(sK0),sK3)
% 14.66/2.53      | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK3),u1_struct_0(sK0)) != iProver_top ),
% 14.66/2.53      inference(light_normalisation,[status(thm)],[c_2833,c_4060]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_5699,plain,
% 14.66/2.53      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)) = k4_xboole_0(u1_struct_0(sK0),sK3) ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_1404,c_5697]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_11,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | ~ l1_pre_topc(X1)
% 14.66/2.53      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 14.66/2.53      inference(cnf_transformation,[],[f55]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_482,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 14.66/2.53      | sK0 != X1 ),
% 14.66/2.53      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_483,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 14.66/2.53      inference(unflattening,[status(thm)],[c_482]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1390,plain,
% 14.66/2.53      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 14.66/2.53      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_2236,plain,
% 14.66/2.53      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_1556,c_1390]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_5016,plain,
% 14.66/2.53      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
% 14.66/2.53      inference(demodulation,[status(thm)],[c_4060,c_2236]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_6001,plain,
% 14.66/2.53      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
% 14.66/2.53      inference(demodulation,[status(thm)],[c_5699,c_5016]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_6,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 14.66/2.53      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 14.66/2.53      inference(cnf_transformation,[],[f50]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_264,plain,
% 14.66/2.53      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 14.66/2.53      inference(bin_hyper_res,[status(thm)],[c_6,c_213]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1394,plain,
% 14.66/2.53      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 14.66/2.53      | r1_tarski(X1,X0) != iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_3344,plain,
% 14.66/2.53      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_1961,c_1394]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_5014,plain,
% 14.66/2.53      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK3)) = sK3 ),
% 14.66/2.53      inference(demodulation,[status(thm)],[c_4060,c_3344]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_6002,plain,
% 14.66/2.53      ( k1_tops_1(sK0,sK3) = sK3 ),
% 14.66/2.53      inference(light_normalisation,[status(thm)],[c_6001,c_5014]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_17,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | ~ r1_tarski(X0,X2)
% 14.66/2.53      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 14.66/2.53      | ~ l1_pre_topc(X1) ),
% 14.66/2.53      inference(cnf_transformation,[],[f61]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_410,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 14.66/2.53      | ~ r1_tarski(X0,X2)
% 14.66/2.53      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 14.66/2.53      | sK0 != X1 ),
% 14.66/2.53      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_411,plain,
% 14.66/2.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.66/2.53      | ~ r1_tarski(X0,X1)
% 14.66/2.53      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 14.66/2.53      inference(unflattening,[status(thm)],[c_410]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1393,plain,
% 14.66/2.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.66/2.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.66/2.53      | r1_tarski(X0,X1) != iProver_top
% 14.66/2.53      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_45988,plain,
% 14.66/2.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.66/2.53      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.66/2.53      | r1_tarski(sK3,X0) != iProver_top
% 14.66/2.53      | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_6002,c_1393]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_47983,plain,
% 14.66/2.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.66/2.53      | r1_tarski(sK3,X0) != iProver_top
% 14.66/2.53      | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
% 14.66/2.53      inference(global_propositional_subsumption,
% 14.66/2.53                [status(thm)],
% 14.66/2.53                [c_45988,c_28,c_29,c_1454,c_1464]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_47991,plain,
% 14.66/2.53      ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top
% 14.66/2.53      | r1_tarski(sK3,sK2) != iProver_top ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_1396,c_47983]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_20,negated_conjecture,
% 14.66/2.53      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(sK3,sK2) ),
% 14.66/2.53      inference(cnf_transformation,[],[f67]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_31,plain,
% 14.66/2.53      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 14.66/2.53      | r1_tarski(sK3,sK2) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_48219,plain,
% 14.66/2.53      ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top ),
% 14.66/2.53      inference(global_propositional_subsumption,
% 14.66/2.53                [status(thm)],
% 14.66/2.53                [c_47991,c_28,c_31,c_1454,c_1464]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_19,negated_conjecture,
% 14.66/2.53      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r2_hidden(sK1,sK3) ),
% 14.66/2.53      inference(cnf_transformation,[],[f68]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1399,plain,
% 14.66/2.53      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 14.66/2.53      | r2_hidden(sK1,sK3) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_32,plain,
% 14.66/2.53      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 14.66/2.53      | r2_hidden(sK1,sK3) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1551,plain,
% 14.66/2.53      ( r2_hidden(sK1,sK3) = iProver_top ),
% 14.66/2.53      inference(global_propositional_subsumption,
% 14.66/2.53                [status(thm)],
% 14.66/2.53                [c_1399,c_28,c_32,c_1454,c_1464]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_3,plain,
% 14.66/2.53      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 14.66/2.53      inference(cnf_transformation,[],[f48]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1403,plain,
% 14.66/2.53      ( r2_hidden(X0,X1) != iProver_top
% 14.66/2.53      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1,plain,
% 14.66/2.53      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 14.66/2.53      inference(cnf_transformation,[],[f45]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1405,plain,
% 14.66/2.53      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_2740,plain,
% 14.66/2.53      ( k2_xboole_0(k1_tarski(X0),X1) = X1
% 14.66/2.53      | r2_hidden(X0,X1) != iProver_top ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_1403,c_1405]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_3395,plain,
% 14.66/2.53      ( k2_xboole_0(k1_tarski(sK1),sK3) = sK3 ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_1551,c_2740]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_0,plain,
% 14.66/2.53      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 14.66/2.53      inference(cnf_transformation,[],[f44]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1406,plain,
% 14.66/2.53      ( r1_tarski(X0,X1) = iProver_top
% 14.66/2.53      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_3609,plain,
% 14.66/2.53      ( r1_tarski(k1_tarski(sK1),X0) = iProver_top
% 14.66/2.53      | r1_tarski(sK3,X0) != iProver_top ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_3395,c_1406]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_4,plain,
% 14.66/2.53      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 14.66/2.53      inference(cnf_transformation,[],[f47]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_1402,plain,
% 14.66/2.53      ( r2_hidden(X0,X1) = iProver_top
% 14.66/2.53      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 14.66/2.53      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_3970,plain,
% 14.66/2.53      ( r2_hidden(sK1,X0) = iProver_top
% 14.66/2.53      | r1_tarski(sK3,X0) != iProver_top ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_3609,c_1402]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(c_48232,plain,
% 14.66/2.53      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 14.66/2.53      inference(superposition,[status(thm)],[c_48219,c_3970]) ).
% 14.66/2.53  
% 14.66/2.53  cnf(contradiction,plain,
% 14.66/2.53      ( $false ),
% 14.66/2.53      inference(minisat,[status(thm)],[c_48232,c_1464,c_1454,c_28]) ).
% 14.66/2.53  
% 14.66/2.53  
% 14.66/2.53  % SZS output end CNFRefutation for theBenchmark.p
% 14.66/2.53  
% 14.66/2.53  ------                               Statistics
% 14.66/2.53  
% 14.66/2.53  ------ General
% 14.66/2.53  
% 14.66/2.53  abstr_ref_over_cycles:                  0
% 14.66/2.53  abstr_ref_under_cycles:                 0
% 14.66/2.53  gc_basic_clause_elim:                   0
% 14.66/2.53  forced_gc_time:                         0
% 14.66/2.53  parsing_time:                           0.014
% 14.66/2.53  unif_index_cands_time:                  0.
% 14.66/2.53  unif_index_add_time:                    0.
% 14.66/2.53  orderings_time:                         0.
% 14.66/2.53  out_proof_time:                         0.02
% 14.66/2.53  total_time:                             1.656
% 14.66/2.53  num_of_symbols:                         50
% 14.66/2.53  num_of_terms:                           41120
% 14.66/2.53  
% 14.66/2.53  ------ Preprocessing
% 14.66/2.53  
% 14.66/2.53  num_of_splits:                          0
% 14.66/2.53  num_of_split_atoms:                     0
% 14.66/2.53  num_of_reused_defs:                     0
% 14.66/2.53  num_eq_ax_congr_red:                    17
% 14.66/2.53  num_of_sem_filtered_clauses:            1
% 14.66/2.53  num_of_subtypes:                        0
% 14.66/2.53  monotx_restored_types:                  0
% 14.66/2.53  sat_num_of_epr_types:                   0
% 14.66/2.53  sat_num_of_non_cyclic_types:            0
% 14.66/2.53  sat_guarded_non_collapsed_types:        0
% 14.66/2.53  num_pure_diseq_elim:                    0
% 14.66/2.53  simp_replaced_by:                       0
% 14.66/2.53  res_preprocessed:                       110
% 14.66/2.53  prep_upred:                             0
% 14.66/2.53  prep_unflattend:                        15
% 14.66/2.53  smt_new_axioms:                         0
% 14.66/2.53  pred_elim_cands:                        3
% 14.66/2.53  pred_elim:                              4
% 14.66/2.53  pred_elim_cl:                           5
% 14.66/2.53  pred_elim_cycles:                       6
% 14.66/2.53  merged_defs:                            16
% 14.66/2.53  merged_defs_ncl:                        0
% 14.66/2.53  bin_hyper_res:                          18
% 14.66/2.53  prep_cycles:                            4
% 14.66/2.53  pred_elim_time:                         0.023
% 14.66/2.53  splitting_time:                         0.
% 14.66/2.53  sem_filter_time:                        0.
% 14.66/2.53  monotx_time:                            0.
% 14.66/2.53  subtype_inf_time:                       0.
% 14.66/2.53  
% 14.66/2.53  ------ Problem properties
% 14.66/2.53  
% 14.66/2.53  clauses:                                21
% 14.66/2.53  conjectures:                            4
% 14.66/2.53  epr:                                    0
% 14.66/2.53  horn:                                   17
% 14.66/2.53  ground:                                 5
% 14.66/2.53  unary:                                  2
% 14.66/2.53  binary:                                 14
% 14.66/2.53  lits:                                   50
% 14.66/2.53  lits_eq:                                7
% 14.66/2.53  fd_pure:                                0
% 14.66/2.53  fd_pseudo:                              0
% 14.66/2.53  fd_cond:                                0
% 14.66/2.53  fd_pseudo_cond:                         0
% 14.66/2.53  ac_symbols:                             0
% 14.66/2.53  
% 14.66/2.53  ------ Propositional Solver
% 14.66/2.53  
% 14.66/2.53  prop_solver_calls:                      32
% 14.66/2.53  prop_fast_solver_calls:                 1798
% 14.66/2.53  smt_solver_calls:                       0
% 14.66/2.53  smt_fast_solver_calls:                  0
% 14.66/2.53  prop_num_of_clauses:                    24739
% 14.66/2.53  prop_preprocess_simplified:             37874
% 14.66/2.53  prop_fo_subsumed:                       59
% 14.66/2.53  prop_solver_time:                       0.
% 14.66/2.53  smt_solver_time:                        0.
% 14.66/2.53  smt_fast_solver_time:                   0.
% 14.66/2.53  prop_fast_solver_time:                  0.
% 14.66/2.53  prop_unsat_core_time:                   0.003
% 14.66/2.53  
% 14.66/2.53  ------ QBF
% 14.66/2.53  
% 14.66/2.53  qbf_q_res:                              0
% 14.66/2.53  qbf_num_tautologies:                    0
% 14.66/2.53  qbf_prep_cycles:                        0
% 14.66/2.53  
% 14.66/2.53  ------ BMC1
% 14.66/2.53  
% 14.66/2.53  bmc1_current_bound:                     -1
% 14.66/2.53  bmc1_last_solved_bound:                 -1
% 14.66/2.53  bmc1_unsat_core_size:                   -1
% 14.66/2.53  bmc1_unsat_core_parents_size:           -1
% 14.66/2.53  bmc1_merge_next_fun:                    0
% 14.66/2.53  bmc1_unsat_core_clauses_time:           0.
% 14.66/2.53  
% 14.66/2.53  ------ Instantiation
% 14.66/2.53  
% 14.66/2.53  inst_num_of_clauses:                    5406
% 14.66/2.53  inst_num_in_passive:                    1747
% 14.66/2.53  inst_num_in_active:                     2353
% 14.66/2.53  inst_num_in_unprocessed:                1307
% 14.66/2.53  inst_num_of_loops:                      2490
% 14.66/2.53  inst_num_of_learning_restarts:          0
% 14.66/2.53  inst_num_moves_active_passive:          136
% 14.66/2.53  inst_lit_activity:                      0
% 14.66/2.53  inst_lit_activity_moves:                2
% 14.66/2.53  inst_num_tautologies:                   0
% 14.66/2.53  inst_num_prop_implied:                  0
% 14.66/2.53  inst_num_existing_simplified:           0
% 14.66/2.53  inst_num_eq_res_simplified:             0
% 14.66/2.53  inst_num_child_elim:                    0
% 14.66/2.53  inst_num_of_dismatching_blockings:      4574
% 14.66/2.53  inst_num_of_non_proper_insts:           4870
% 14.66/2.53  inst_num_of_duplicates:                 0
% 14.66/2.53  inst_inst_num_from_inst_to_res:         0
% 14.66/2.53  inst_dismatching_checking_time:         0.
% 14.66/2.53  
% 14.66/2.53  ------ Resolution
% 14.66/2.53  
% 14.66/2.53  res_num_of_clauses:                     0
% 14.66/2.53  res_num_in_passive:                     0
% 14.66/2.53  res_num_in_active:                      0
% 14.66/2.53  res_num_of_loops:                       114
% 14.66/2.53  res_forward_subset_subsumed:            198
% 14.66/2.53  res_backward_subset_subsumed:           2
% 14.66/2.53  res_forward_subsumed:                   0
% 14.66/2.53  res_backward_subsumed:                  0
% 14.66/2.53  res_forward_subsumption_resolution:     0
% 14.66/2.53  res_backward_subsumption_resolution:    0
% 14.66/2.53  res_clause_to_clause_subsumption:       14241
% 14.66/2.53  res_orphan_elimination:                 0
% 14.66/2.53  res_tautology_del:                      308
% 14.66/2.53  res_num_eq_res_simplified:              0
% 14.66/2.53  res_num_sel_changes:                    0
% 14.66/2.53  res_moves_from_active_to_pass:          0
% 14.66/2.53  
% 14.66/2.53  ------ Superposition
% 14.66/2.53  
% 14.66/2.53  sup_time_total:                         0.
% 14.66/2.53  sup_time_generating:                    0.
% 14.66/2.53  sup_time_sim_full:                      0.
% 14.66/2.53  sup_time_sim_immed:                     0.
% 14.66/2.53  
% 14.66/2.53  sup_num_of_clauses:                     1973
% 14.66/2.53  sup_num_in_active:                      462
% 14.66/2.53  sup_num_in_passive:                     1511
% 14.66/2.53  sup_num_of_loops:                       496
% 14.66/2.53  sup_fw_superposition:                   2581
% 14.66/2.53  sup_bw_superposition:                   742
% 14.66/2.53  sup_immediate_simplified:               919
% 14.66/2.53  sup_given_eliminated:                   0
% 14.66/2.53  comparisons_done:                       0
% 14.66/2.53  comparisons_avoided:                    0
% 14.66/2.53  
% 14.66/2.53  ------ Simplifications
% 14.66/2.53  
% 14.66/2.53  
% 14.66/2.53  sim_fw_subset_subsumed:                 118
% 14.66/2.53  sim_bw_subset_subsumed:                 119
% 14.66/2.53  sim_fw_subsumed:                        127
% 14.66/2.53  sim_bw_subsumed:                        5
% 14.66/2.53  sim_fw_subsumption_res:                 0
% 14.66/2.53  sim_bw_subsumption_res:                 0
% 14.66/2.53  sim_tautology_del:                      9
% 14.66/2.53  sim_eq_tautology_del:                   433
% 14.66/2.53  sim_eq_res_simp:                        0
% 14.66/2.53  sim_fw_demodulated:                     170
% 14.66/2.53  sim_bw_demodulated:                     31
% 14.66/2.53  sim_light_normalised:                   775
% 14.66/2.53  sim_joinable_taut:                      0
% 14.66/2.53  sim_joinable_simp:                      0
% 14.66/2.53  sim_ac_normalised:                      0
% 14.66/2.53  sim_smt_subsumption:                    0
% 14.66/2.53  
%------------------------------------------------------------------------------
