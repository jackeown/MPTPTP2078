%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:01 EST 2020

% Result     : Theorem 11.75s
% Output     : CNFRefutation 11.75s
% Verified   : 
% Statistics : Number of formulae       :  180 (2550 expanded)
%              Number of clauses        :  122 ( 732 expanded)
%              Number of leaves         :   15 ( 590 expanded)
%              Depth                    :   27
%              Number of atoms          :  628 (20085 expanded)
%              Number of equality atoms :  197 ( 653 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f37,f36,f35])).

fof(f56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1337,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1331,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1335,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | r2_hidden(sK1,X0) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1539,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | r2_hidden(sK1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1331,c_1335])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_25,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_303,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_304,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_20])).

cnf(c_309,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_308])).

cnf(c_1373,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_1374,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1373])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_1392,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_1437,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1438,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1437])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1454,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1546,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_1547,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1546])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1483,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1627,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_1826,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1627])).

cnf(c_1827,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1826])).

cnf(c_1376,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1959,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_1960,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1959])).

cnf(c_2641,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1539,c_24,c_25,c_1374,c_1392,c_1438,c_1547,c_1827,c_1960])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_421,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_422,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_379,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_380,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_479,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) = X1
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_422,c_380])).

cnf(c_480,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_1322,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_481,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_1486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1487,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_168,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_169,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_168])).

cnf(c_214,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_169])).

cnf(c_1497,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_1498,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1497])).

cnf(c_1693,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1322,c_481,c_1487,c_1498])).

cnf(c_1694,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1693])).

cnf(c_2649,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | v3_pre_topc(sK3,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2641,c_1694])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_531,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | sK3 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_480,c_17])).

cnf(c_532,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_534,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_18])).

cnf(c_535,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(renaming,[status(thm)],[c_534])).

cnf(c_1797,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(X2))
    | r1_tarski(X0,u1_struct_0(X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2374,plain,
    ( r1_tarski(sK3,u1_struct_0(X0))
    | ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(c_2376,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_2568,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_3499,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2649,c_19,c_16,c_535,c_1373,c_1391,c_1437,c_1546,c_1826,c_1959,c_2376,c_2568])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_1324,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_2647,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_2641,c_1324])).

cnf(c_3501,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_3499,c_2647])).

cnf(c_1336,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2645,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2641,c_1336])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_215,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_169])).

cnf(c_1328,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_2741,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2645,c_1328])).

cnf(c_3502,plain,
    ( k1_tops_1(sK0,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3501,c_2741])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_1326,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_36696,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3502,c_1326])).

cnf(c_37345,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36696,c_24,c_25,c_1374,c_1392,c_1438,c_1547,c_1827,c_1960])).

cnf(c_37351,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_37345])).

cnf(c_1330,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1339,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2200,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,k1_tops_1(sK0,X0)) != iProver_top
    | r1_tarski(X2,k1_tops_1(sK0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1326,c_1339])).

cnf(c_4352,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,k1_tops_1(sK0,X1)) != iProver_top
    | r1_tarski(X2,k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_2200])).

cnf(c_7189,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1330,c_4352])).

cnf(c_38575,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_37351,c_7189])).

cnf(c_27,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1325,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_2650,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2641,c_1325])).

cnf(c_7415,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X1,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1326,c_7189])).

cnf(c_1377,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1376])).

cnf(c_1484,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_23917,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X1,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7415,c_1377,c_1484])).

cnf(c_23918,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_23917])).

cnf(c_1628,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1627])).

cnf(c_23921,plain,
    ( r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23918,c_24,c_1377,c_1547,c_1628])).

cnf(c_23922,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_23921])).

cnf(c_23944,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK3)),k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2650,c_23922])).

cnf(c_23972,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23944,c_3502])).

cnf(c_38876,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38575,c_24,c_27,c_1374,c_1392,c_1438,c_1547,c_1827,c_1960,c_23972])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1334,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1534,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | r2_hidden(sK1,X0) != iProver_top
    | r2_hidden(sK1,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_1335])).

cnf(c_28,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2636,plain,
    ( r2_hidden(sK1,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1534,c_24,c_28,c_1374,c_1392,c_1438,c_1547,c_1827,c_1960])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1338,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1860,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1338])).

cnf(c_3591,plain,
    ( r2_hidden(sK1,X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2636,c_1860])).

cnf(c_38912,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_38876,c_3591])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38912,c_1960,c_1827,c_1547,c_1438,c_1392,c_1374,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.75/2.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.75/2.02  
% 11.75/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.75/2.02  
% 11.75/2.02  ------  iProver source info
% 11.75/2.02  
% 11.75/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.75/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.75/2.02  git: non_committed_changes: false
% 11.75/2.02  git: last_make_outside_of_git: false
% 11.75/2.02  
% 11.75/2.02  ------ 
% 11.75/2.02  
% 11.75/2.02  ------ Input Options
% 11.75/2.02  
% 11.75/2.02  --out_options                           all
% 11.75/2.02  --tptp_safe_out                         true
% 11.75/2.02  --problem_path                          ""
% 11.75/2.02  --include_path                          ""
% 11.75/2.02  --clausifier                            res/vclausify_rel
% 11.75/2.02  --clausifier_options                    ""
% 11.75/2.02  --stdin                                 false
% 11.75/2.02  --stats_out                             all
% 11.75/2.02  
% 11.75/2.02  ------ General Options
% 11.75/2.02  
% 11.75/2.02  --fof                                   false
% 11.75/2.02  --time_out_real                         305.
% 11.75/2.02  --time_out_virtual                      -1.
% 11.75/2.02  --symbol_type_check                     false
% 11.75/2.02  --clausify_out                          false
% 11.75/2.02  --sig_cnt_out                           false
% 11.75/2.02  --trig_cnt_out                          false
% 11.75/2.02  --trig_cnt_out_tolerance                1.
% 11.75/2.02  --trig_cnt_out_sk_spl                   false
% 11.75/2.02  --abstr_cl_out                          false
% 11.75/2.02  
% 11.75/2.02  ------ Global Options
% 11.75/2.02  
% 11.75/2.02  --schedule                              default
% 11.75/2.02  --add_important_lit                     false
% 11.75/2.02  --prop_solver_per_cl                    1000
% 11.75/2.02  --min_unsat_core                        false
% 11.75/2.02  --soft_assumptions                      false
% 11.75/2.02  --soft_lemma_size                       3
% 11.75/2.02  --prop_impl_unit_size                   0
% 11.75/2.02  --prop_impl_unit                        []
% 11.75/2.02  --share_sel_clauses                     true
% 11.75/2.02  --reset_solvers                         false
% 11.75/2.02  --bc_imp_inh                            [conj_cone]
% 11.75/2.02  --conj_cone_tolerance                   3.
% 11.75/2.02  --extra_neg_conj                        none
% 11.75/2.02  --large_theory_mode                     true
% 11.75/2.02  --prolific_symb_bound                   200
% 11.75/2.02  --lt_threshold                          2000
% 11.75/2.02  --clause_weak_htbl                      true
% 11.75/2.02  --gc_record_bc_elim                     false
% 11.75/2.02  
% 11.75/2.02  ------ Preprocessing Options
% 11.75/2.02  
% 11.75/2.02  --preprocessing_flag                    true
% 11.75/2.02  --time_out_prep_mult                    0.1
% 11.75/2.02  --splitting_mode                        input
% 11.75/2.02  --splitting_grd                         true
% 11.75/2.02  --splitting_cvd                         false
% 11.75/2.02  --splitting_cvd_svl                     false
% 11.75/2.02  --splitting_nvd                         32
% 11.75/2.02  --sub_typing                            true
% 11.75/2.02  --prep_gs_sim                           true
% 11.75/2.02  --prep_unflatten                        true
% 11.75/2.02  --prep_res_sim                          true
% 11.75/2.02  --prep_upred                            true
% 11.75/2.02  --prep_sem_filter                       exhaustive
% 11.75/2.02  --prep_sem_filter_out                   false
% 11.75/2.02  --pred_elim                             true
% 11.75/2.02  --res_sim_input                         true
% 11.75/2.02  --eq_ax_congr_red                       true
% 11.75/2.02  --pure_diseq_elim                       true
% 11.75/2.02  --brand_transform                       false
% 11.75/2.02  --non_eq_to_eq                          false
% 11.75/2.02  --prep_def_merge                        true
% 11.75/2.02  --prep_def_merge_prop_impl              false
% 11.75/2.02  --prep_def_merge_mbd                    true
% 11.75/2.02  --prep_def_merge_tr_red                 false
% 11.75/2.02  --prep_def_merge_tr_cl                  false
% 11.75/2.02  --smt_preprocessing                     true
% 11.75/2.02  --smt_ac_axioms                         fast
% 11.75/2.02  --preprocessed_out                      false
% 11.75/2.02  --preprocessed_stats                    false
% 11.75/2.02  
% 11.75/2.02  ------ Abstraction refinement Options
% 11.75/2.02  
% 11.75/2.02  --abstr_ref                             []
% 11.75/2.02  --abstr_ref_prep                        false
% 11.75/2.02  --abstr_ref_until_sat                   false
% 11.75/2.02  --abstr_ref_sig_restrict                funpre
% 11.75/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.75/2.02  --abstr_ref_under                       []
% 11.75/2.02  
% 11.75/2.02  ------ SAT Options
% 11.75/2.02  
% 11.75/2.02  --sat_mode                              false
% 11.75/2.02  --sat_fm_restart_options                ""
% 11.75/2.02  --sat_gr_def                            false
% 11.75/2.02  --sat_epr_types                         true
% 11.75/2.02  --sat_non_cyclic_types                  false
% 11.75/2.02  --sat_finite_models                     false
% 11.75/2.02  --sat_fm_lemmas                         false
% 11.75/2.02  --sat_fm_prep                           false
% 11.75/2.02  --sat_fm_uc_incr                        true
% 11.75/2.02  --sat_out_model                         small
% 11.75/2.02  --sat_out_clauses                       false
% 11.75/2.02  
% 11.75/2.02  ------ QBF Options
% 11.75/2.02  
% 11.75/2.02  --qbf_mode                              false
% 11.75/2.02  --qbf_elim_univ                         false
% 11.75/2.02  --qbf_dom_inst                          none
% 11.75/2.02  --qbf_dom_pre_inst                      false
% 11.75/2.02  --qbf_sk_in                             false
% 11.75/2.02  --qbf_pred_elim                         true
% 11.75/2.02  --qbf_split                             512
% 11.75/2.02  
% 11.75/2.02  ------ BMC1 Options
% 11.75/2.02  
% 11.75/2.02  --bmc1_incremental                      false
% 11.75/2.02  --bmc1_axioms                           reachable_all
% 11.75/2.02  --bmc1_min_bound                        0
% 11.75/2.02  --bmc1_max_bound                        -1
% 11.75/2.02  --bmc1_max_bound_default                -1
% 11.75/2.02  --bmc1_symbol_reachability              true
% 11.75/2.02  --bmc1_property_lemmas                  false
% 11.75/2.02  --bmc1_k_induction                      false
% 11.75/2.02  --bmc1_non_equiv_states                 false
% 11.75/2.02  --bmc1_deadlock                         false
% 11.75/2.02  --bmc1_ucm                              false
% 11.75/2.02  --bmc1_add_unsat_core                   none
% 11.75/2.02  --bmc1_unsat_core_children              false
% 11.75/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.75/2.02  --bmc1_out_stat                         full
% 11.75/2.02  --bmc1_ground_init                      false
% 11.75/2.02  --bmc1_pre_inst_next_state              false
% 11.75/2.02  --bmc1_pre_inst_state                   false
% 11.75/2.02  --bmc1_pre_inst_reach_state             false
% 11.75/2.02  --bmc1_out_unsat_core                   false
% 11.75/2.02  --bmc1_aig_witness_out                  false
% 11.75/2.02  --bmc1_verbose                          false
% 11.75/2.02  --bmc1_dump_clauses_tptp                false
% 11.75/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.75/2.02  --bmc1_dump_file                        -
% 11.75/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.75/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.75/2.02  --bmc1_ucm_extend_mode                  1
% 11.75/2.02  --bmc1_ucm_init_mode                    2
% 11.75/2.02  --bmc1_ucm_cone_mode                    none
% 11.75/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.75/2.02  --bmc1_ucm_relax_model                  4
% 11.75/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.75/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.75/2.02  --bmc1_ucm_layered_model                none
% 11.75/2.02  --bmc1_ucm_max_lemma_size               10
% 11.75/2.02  
% 11.75/2.02  ------ AIG Options
% 11.75/2.02  
% 11.75/2.02  --aig_mode                              false
% 11.75/2.02  
% 11.75/2.02  ------ Instantiation Options
% 11.75/2.02  
% 11.75/2.02  --instantiation_flag                    true
% 11.75/2.02  --inst_sos_flag                         true
% 11.75/2.02  --inst_sos_phase                        true
% 11.75/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.75/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.75/2.02  --inst_lit_sel_side                     num_symb
% 11.75/2.02  --inst_solver_per_active                1400
% 11.75/2.02  --inst_solver_calls_frac                1.
% 11.75/2.02  --inst_passive_queue_type               priority_queues
% 11.75/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.75/2.02  --inst_passive_queues_freq              [25;2]
% 11.75/2.02  --inst_dismatching                      true
% 11.75/2.02  --inst_eager_unprocessed_to_passive     true
% 11.75/2.02  --inst_prop_sim_given                   true
% 11.75/2.02  --inst_prop_sim_new                     false
% 11.75/2.02  --inst_subs_new                         false
% 11.75/2.02  --inst_eq_res_simp                      false
% 11.75/2.02  --inst_subs_given                       false
% 11.75/2.02  --inst_orphan_elimination               true
% 11.75/2.02  --inst_learning_loop_flag               true
% 11.75/2.02  --inst_learning_start                   3000
% 11.75/2.02  --inst_learning_factor                  2
% 11.75/2.02  --inst_start_prop_sim_after_learn       3
% 11.75/2.02  --inst_sel_renew                        solver
% 11.75/2.02  --inst_lit_activity_flag                true
% 11.75/2.02  --inst_restr_to_given                   false
% 11.75/2.02  --inst_activity_threshold               500
% 11.75/2.02  --inst_out_proof                        true
% 11.75/2.02  
% 11.75/2.02  ------ Resolution Options
% 11.75/2.02  
% 11.75/2.02  --resolution_flag                       true
% 11.75/2.02  --res_lit_sel                           adaptive
% 11.75/2.02  --res_lit_sel_side                      none
% 11.75/2.02  --res_ordering                          kbo
% 11.75/2.02  --res_to_prop_solver                    active
% 11.75/2.02  --res_prop_simpl_new                    false
% 11.75/2.02  --res_prop_simpl_given                  true
% 11.75/2.02  --res_passive_queue_type                priority_queues
% 11.75/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.75/2.02  --res_passive_queues_freq               [15;5]
% 11.75/2.02  --res_forward_subs                      full
% 11.75/2.02  --res_backward_subs                     full
% 11.75/2.02  --res_forward_subs_resolution           true
% 11.75/2.02  --res_backward_subs_resolution          true
% 11.75/2.02  --res_orphan_elimination                true
% 11.75/2.02  --res_time_limit                        2.
% 11.75/2.02  --res_out_proof                         true
% 11.75/2.02  
% 11.75/2.02  ------ Superposition Options
% 11.75/2.02  
% 11.75/2.02  --superposition_flag                    true
% 11.75/2.02  --sup_passive_queue_type                priority_queues
% 11.75/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.75/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.75/2.02  --demod_completeness_check              fast
% 11.75/2.02  --demod_use_ground                      true
% 11.75/2.02  --sup_to_prop_solver                    passive
% 11.75/2.02  --sup_prop_simpl_new                    true
% 11.75/2.02  --sup_prop_simpl_given                  true
% 11.75/2.02  --sup_fun_splitting                     true
% 11.75/2.02  --sup_smt_interval                      50000
% 11.75/2.02  
% 11.75/2.02  ------ Superposition Simplification Setup
% 11.75/2.02  
% 11.75/2.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.75/2.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.75/2.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.75/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.75/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.75/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.75/2.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.75/2.02  --sup_immed_triv                        [TrivRules]
% 11.75/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/2.02  --sup_immed_bw_main                     []
% 11.75/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.75/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.75/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/2.02  --sup_input_bw                          []
% 11.75/2.02  
% 11.75/2.02  ------ Combination Options
% 11.75/2.02  
% 11.75/2.02  --comb_res_mult                         3
% 11.75/2.02  --comb_sup_mult                         2
% 11.75/2.02  --comb_inst_mult                        10
% 11.75/2.02  
% 11.75/2.02  ------ Debug Options
% 11.75/2.02  
% 11.75/2.02  --dbg_backtrace                         false
% 11.75/2.02  --dbg_dump_prop_clauses                 false
% 11.75/2.02  --dbg_dump_prop_clauses_file            -
% 11.75/2.02  --dbg_out_stat                          false
% 11.75/2.02  ------ Parsing...
% 11.75/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.75/2.02  
% 11.75/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.75/2.02  
% 11.75/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.75/2.02  
% 11.75/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.75/2.02  ------ Proving...
% 11.75/2.02  ------ Problem Properties 
% 11.75/2.02  
% 11.75/2.02  
% 11.75/2.02  clauses                                 18
% 11.75/2.02  conjectures                             6
% 11.75/2.02  EPR                                     1
% 11.75/2.02  Horn                                    14
% 11.75/2.02  unary                                   1
% 11.75/2.02  binary                                  11
% 11.75/2.02  lits                                    46
% 11.75/2.02  lits eq                                 4
% 11.75/2.02  fd_pure                                 0
% 11.75/2.02  fd_pseudo                               0
% 11.75/2.02  fd_cond                                 0
% 11.75/2.02  fd_pseudo_cond                          0
% 11.75/2.02  AC symbols                              0
% 11.75/2.02  
% 11.75/2.02  ------ Schedule dynamic 5 is on 
% 11.75/2.02  
% 11.75/2.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.75/2.02  
% 11.75/2.02  
% 11.75/2.02  ------ 
% 11.75/2.02  Current options:
% 11.75/2.02  ------ 
% 11.75/2.02  
% 11.75/2.02  ------ Input Options
% 11.75/2.02  
% 11.75/2.02  --out_options                           all
% 11.75/2.02  --tptp_safe_out                         true
% 11.75/2.02  --problem_path                          ""
% 11.75/2.02  --include_path                          ""
% 11.75/2.02  --clausifier                            res/vclausify_rel
% 11.75/2.02  --clausifier_options                    ""
% 11.75/2.02  --stdin                                 false
% 11.75/2.02  --stats_out                             all
% 11.75/2.02  
% 11.75/2.02  ------ General Options
% 11.75/2.02  
% 11.75/2.02  --fof                                   false
% 11.75/2.02  --time_out_real                         305.
% 11.75/2.02  --time_out_virtual                      -1.
% 11.75/2.02  --symbol_type_check                     false
% 11.75/2.02  --clausify_out                          false
% 11.75/2.02  --sig_cnt_out                           false
% 11.75/2.02  --trig_cnt_out                          false
% 11.75/2.02  --trig_cnt_out_tolerance                1.
% 11.75/2.02  --trig_cnt_out_sk_spl                   false
% 11.75/2.02  --abstr_cl_out                          false
% 11.75/2.02  
% 11.75/2.02  ------ Global Options
% 11.75/2.02  
% 11.75/2.02  --schedule                              default
% 11.75/2.02  --add_important_lit                     false
% 11.75/2.02  --prop_solver_per_cl                    1000
% 11.75/2.02  --min_unsat_core                        false
% 11.75/2.02  --soft_assumptions                      false
% 11.75/2.02  --soft_lemma_size                       3
% 11.75/2.02  --prop_impl_unit_size                   0
% 11.75/2.02  --prop_impl_unit                        []
% 11.75/2.02  --share_sel_clauses                     true
% 11.75/2.02  --reset_solvers                         false
% 11.75/2.02  --bc_imp_inh                            [conj_cone]
% 11.75/2.02  --conj_cone_tolerance                   3.
% 11.75/2.02  --extra_neg_conj                        none
% 11.75/2.02  --large_theory_mode                     true
% 11.75/2.02  --prolific_symb_bound                   200
% 11.75/2.02  --lt_threshold                          2000
% 11.75/2.02  --clause_weak_htbl                      true
% 11.75/2.02  --gc_record_bc_elim                     false
% 11.75/2.02  
% 11.75/2.02  ------ Preprocessing Options
% 11.75/2.02  
% 11.75/2.02  --preprocessing_flag                    true
% 11.75/2.02  --time_out_prep_mult                    0.1
% 11.75/2.02  --splitting_mode                        input
% 11.75/2.02  --splitting_grd                         true
% 11.75/2.02  --splitting_cvd                         false
% 11.75/2.02  --splitting_cvd_svl                     false
% 11.75/2.02  --splitting_nvd                         32
% 11.75/2.02  --sub_typing                            true
% 11.75/2.02  --prep_gs_sim                           true
% 11.75/2.02  --prep_unflatten                        true
% 11.75/2.02  --prep_res_sim                          true
% 11.75/2.02  --prep_upred                            true
% 11.75/2.02  --prep_sem_filter                       exhaustive
% 11.75/2.02  --prep_sem_filter_out                   false
% 11.75/2.02  --pred_elim                             true
% 11.75/2.02  --res_sim_input                         true
% 11.75/2.02  --eq_ax_congr_red                       true
% 11.75/2.02  --pure_diseq_elim                       true
% 11.75/2.02  --brand_transform                       false
% 11.75/2.02  --non_eq_to_eq                          false
% 11.75/2.02  --prep_def_merge                        true
% 11.75/2.02  --prep_def_merge_prop_impl              false
% 11.75/2.02  --prep_def_merge_mbd                    true
% 11.75/2.02  --prep_def_merge_tr_red                 false
% 11.75/2.02  --prep_def_merge_tr_cl                  false
% 11.75/2.02  --smt_preprocessing                     true
% 11.75/2.02  --smt_ac_axioms                         fast
% 11.75/2.02  --preprocessed_out                      false
% 11.75/2.02  --preprocessed_stats                    false
% 11.75/2.02  
% 11.75/2.02  ------ Abstraction refinement Options
% 11.75/2.02  
% 11.75/2.02  --abstr_ref                             []
% 11.75/2.02  --abstr_ref_prep                        false
% 11.75/2.02  --abstr_ref_until_sat                   false
% 11.75/2.02  --abstr_ref_sig_restrict                funpre
% 11.75/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.75/2.02  --abstr_ref_under                       []
% 11.75/2.02  
% 11.75/2.02  ------ SAT Options
% 11.75/2.02  
% 11.75/2.02  --sat_mode                              false
% 11.75/2.02  --sat_fm_restart_options                ""
% 11.75/2.02  --sat_gr_def                            false
% 11.75/2.02  --sat_epr_types                         true
% 11.75/2.02  --sat_non_cyclic_types                  false
% 11.75/2.02  --sat_finite_models                     false
% 11.75/2.02  --sat_fm_lemmas                         false
% 11.75/2.02  --sat_fm_prep                           false
% 11.75/2.02  --sat_fm_uc_incr                        true
% 11.75/2.02  --sat_out_model                         small
% 11.75/2.02  --sat_out_clauses                       false
% 11.75/2.02  
% 11.75/2.02  ------ QBF Options
% 11.75/2.02  
% 11.75/2.02  --qbf_mode                              false
% 11.75/2.02  --qbf_elim_univ                         false
% 11.75/2.02  --qbf_dom_inst                          none
% 11.75/2.02  --qbf_dom_pre_inst                      false
% 11.75/2.02  --qbf_sk_in                             false
% 11.75/2.02  --qbf_pred_elim                         true
% 11.75/2.02  --qbf_split                             512
% 11.75/2.02  
% 11.75/2.02  ------ BMC1 Options
% 11.75/2.02  
% 11.75/2.02  --bmc1_incremental                      false
% 11.75/2.02  --bmc1_axioms                           reachable_all
% 11.75/2.02  --bmc1_min_bound                        0
% 11.75/2.02  --bmc1_max_bound                        -1
% 11.75/2.02  --bmc1_max_bound_default                -1
% 11.75/2.02  --bmc1_symbol_reachability              true
% 11.75/2.02  --bmc1_property_lemmas                  false
% 11.75/2.02  --bmc1_k_induction                      false
% 11.75/2.02  --bmc1_non_equiv_states                 false
% 11.75/2.02  --bmc1_deadlock                         false
% 11.75/2.02  --bmc1_ucm                              false
% 11.75/2.02  --bmc1_add_unsat_core                   none
% 11.75/2.02  --bmc1_unsat_core_children              false
% 11.75/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.75/2.02  --bmc1_out_stat                         full
% 11.75/2.02  --bmc1_ground_init                      false
% 11.75/2.02  --bmc1_pre_inst_next_state              false
% 11.75/2.02  --bmc1_pre_inst_state                   false
% 11.75/2.02  --bmc1_pre_inst_reach_state             false
% 11.75/2.02  --bmc1_out_unsat_core                   false
% 11.75/2.02  --bmc1_aig_witness_out                  false
% 11.75/2.02  --bmc1_verbose                          false
% 11.75/2.02  --bmc1_dump_clauses_tptp                false
% 11.75/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.75/2.02  --bmc1_dump_file                        -
% 11.75/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.75/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.75/2.02  --bmc1_ucm_extend_mode                  1
% 11.75/2.02  --bmc1_ucm_init_mode                    2
% 11.75/2.02  --bmc1_ucm_cone_mode                    none
% 11.75/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.75/2.02  --bmc1_ucm_relax_model                  4
% 11.75/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.75/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.75/2.02  --bmc1_ucm_layered_model                none
% 11.75/2.02  --bmc1_ucm_max_lemma_size               10
% 11.75/2.02  
% 11.75/2.02  ------ AIG Options
% 11.75/2.02  
% 11.75/2.02  --aig_mode                              false
% 11.75/2.02  
% 11.75/2.02  ------ Instantiation Options
% 11.75/2.02  
% 11.75/2.02  --instantiation_flag                    true
% 11.75/2.02  --inst_sos_flag                         true
% 11.75/2.02  --inst_sos_phase                        true
% 11.75/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.75/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.75/2.02  --inst_lit_sel_side                     none
% 11.75/2.02  --inst_solver_per_active                1400
% 11.75/2.02  --inst_solver_calls_frac                1.
% 11.75/2.02  --inst_passive_queue_type               priority_queues
% 11.75/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.75/2.02  --inst_passive_queues_freq              [25;2]
% 11.75/2.02  --inst_dismatching                      true
% 11.75/2.02  --inst_eager_unprocessed_to_passive     true
% 11.75/2.02  --inst_prop_sim_given                   true
% 11.75/2.02  --inst_prop_sim_new                     false
% 11.75/2.02  --inst_subs_new                         false
% 11.75/2.02  --inst_eq_res_simp                      false
% 11.75/2.02  --inst_subs_given                       false
% 11.75/2.02  --inst_orphan_elimination               true
% 11.75/2.02  --inst_learning_loop_flag               true
% 11.75/2.02  --inst_learning_start                   3000
% 11.75/2.02  --inst_learning_factor                  2
% 11.75/2.02  --inst_start_prop_sim_after_learn       3
% 11.75/2.02  --inst_sel_renew                        solver
% 11.75/2.02  --inst_lit_activity_flag                true
% 11.75/2.02  --inst_restr_to_given                   false
% 11.75/2.02  --inst_activity_threshold               500
% 11.75/2.02  --inst_out_proof                        true
% 11.75/2.02  
% 11.75/2.02  ------ Resolution Options
% 11.75/2.02  
% 11.75/2.02  --resolution_flag                       false
% 11.75/2.02  --res_lit_sel                           adaptive
% 11.75/2.02  --res_lit_sel_side                      none
% 11.75/2.02  --res_ordering                          kbo
% 11.75/2.02  --res_to_prop_solver                    active
% 11.75/2.02  --res_prop_simpl_new                    false
% 11.75/2.02  --res_prop_simpl_given                  true
% 11.75/2.02  --res_passive_queue_type                priority_queues
% 11.75/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.75/2.02  --res_passive_queues_freq               [15;5]
% 11.75/2.02  --res_forward_subs                      full
% 11.75/2.02  --res_backward_subs                     full
% 11.75/2.02  --res_forward_subs_resolution           true
% 11.75/2.02  --res_backward_subs_resolution          true
% 11.75/2.02  --res_orphan_elimination                true
% 11.75/2.02  --res_time_limit                        2.
% 11.75/2.02  --res_out_proof                         true
% 11.75/2.02  
% 11.75/2.02  ------ Superposition Options
% 11.75/2.02  
% 11.75/2.02  --superposition_flag                    true
% 11.75/2.02  --sup_passive_queue_type                priority_queues
% 11.75/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.75/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.75/2.02  --demod_completeness_check              fast
% 11.75/2.02  --demod_use_ground                      true
% 11.75/2.02  --sup_to_prop_solver                    passive
% 11.75/2.02  --sup_prop_simpl_new                    true
% 11.75/2.02  --sup_prop_simpl_given                  true
% 11.75/2.02  --sup_fun_splitting                     true
% 11.75/2.02  --sup_smt_interval                      50000
% 11.75/2.02  
% 11.75/2.02  ------ Superposition Simplification Setup
% 11.75/2.02  
% 11.75/2.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.75/2.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.75/2.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.75/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.75/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.75/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.75/2.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.75/2.02  --sup_immed_triv                        [TrivRules]
% 11.75/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/2.02  --sup_immed_bw_main                     []
% 11.75/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.75/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.75/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/2.02  --sup_input_bw                          []
% 11.75/2.02  
% 11.75/2.02  ------ Combination Options
% 11.75/2.02  
% 11.75/2.02  --comb_res_mult                         3
% 11.75/2.02  --comb_sup_mult                         2
% 11.75/2.02  --comb_inst_mult                        10
% 11.75/2.02  
% 11.75/2.02  ------ Debug Options
% 11.75/2.02  
% 11.75/2.02  --dbg_backtrace                         false
% 11.75/2.02  --dbg_dump_prop_clauses                 false
% 11.75/2.02  --dbg_dump_prop_clauses_file            -
% 11.75/2.02  --dbg_out_stat                          false
% 11.75/2.02  
% 11.75/2.02  
% 11.75/2.02  
% 11.75/2.02  
% 11.75/2.02  ------ Proving...
% 11.75/2.02  
% 11.75/2.02  
% 11.75/2.02  % SZS status Theorem for theBenchmark.p
% 11.75/2.02  
% 11.75/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.75/2.02  
% 11.75/2.02  fof(f5,axiom,(
% 11.75/2.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f30,plain,(
% 11.75/2.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.75/2.02    inference(nnf_transformation,[],[f5])).
% 11.75/2.02  
% 11.75/2.02  fof(f44,plain,(
% 11.75/2.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.75/2.02    inference(cnf_transformation,[],[f30])).
% 11.75/2.02  
% 11.75/2.02  fof(f12,conjecture,(
% 11.75/2.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f13,negated_conjecture,(
% 11.75/2.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 11.75/2.02    inference(negated_conjecture,[],[f12])).
% 11.75/2.02  
% 11.75/2.02  fof(f28,plain,(
% 11.75/2.02    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.75/2.02    inference(ennf_transformation,[],[f13])).
% 11.75/2.02  
% 11.75/2.02  fof(f29,plain,(
% 11.75/2.02    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.75/2.02    inference(flattening,[],[f28])).
% 11.75/2.02  
% 11.75/2.02  fof(f32,plain,(
% 11.75/2.02    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.75/2.02    inference(nnf_transformation,[],[f29])).
% 11.75/2.02  
% 11.75/2.02  fof(f33,plain,(
% 11.75/2.02    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.75/2.02    inference(flattening,[],[f32])).
% 11.75/2.02  
% 11.75/2.02  fof(f34,plain,(
% 11.75/2.02    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.75/2.02    inference(rectify,[],[f33])).
% 11.75/2.02  
% 11.75/2.02  fof(f37,plain,(
% 11.75/2.02    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3) & r1_tarski(sK3,X2) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.75/2.02    introduced(choice_axiom,[])).
% 11.75/2.02  
% 11.75/2.02  fof(f36,plain,(
% 11.75/2.02    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK1,k1_tops_1(X0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK1,k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.75/2.02    introduced(choice_axiom,[])).
% 11.75/2.02  
% 11.75/2.02  fof(f35,plain,(
% 11.75/2.02    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.75/2.02    introduced(choice_axiom,[])).
% 11.75/2.02  
% 11.75/2.02  fof(f38,plain,(
% 11.75/2.02    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.75/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 11.75/2.02  
% 11.75/2.02  fof(f56,plain,(
% 11.75/2.02    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 11.75/2.02    inference(cnf_transformation,[],[f38])).
% 11.75/2.02  
% 11.75/2.02  fof(f60,plain,(
% 11.75/2.02    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 11.75/2.02    inference(cnf_transformation,[],[f38])).
% 11.75/2.02  
% 11.75/2.02  fof(f55,plain,(
% 11.75/2.02    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.75/2.02    inference(cnf_transformation,[],[f38])).
% 11.75/2.02  
% 11.75/2.02  fof(f8,axiom,(
% 11.75/2.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f22,plain,(
% 11.75/2.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.75/2.02    inference(ennf_transformation,[],[f8])).
% 11.75/2.02  
% 11.75/2.02  fof(f23,plain,(
% 11.75/2.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.75/2.02    inference(flattening,[],[f22])).
% 11.75/2.02  
% 11.75/2.02  fof(f48,plain,(
% 11.75/2.02    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.75/2.02    inference(cnf_transformation,[],[f23])).
% 11.75/2.02  
% 11.75/2.02  fof(f53,plain,(
% 11.75/2.02    v2_pre_topc(sK0)),
% 11.75/2.02    inference(cnf_transformation,[],[f38])).
% 11.75/2.02  
% 11.75/2.02  fof(f54,plain,(
% 11.75/2.02    l1_pre_topc(sK0)),
% 11.75/2.02    inference(cnf_transformation,[],[f38])).
% 11.75/2.02  
% 11.75/2.02  fof(f10,axiom,(
% 11.75/2.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f25,plain,(
% 11.75/2.02    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/2.02    inference(ennf_transformation,[],[f10])).
% 11.75/2.02  
% 11.75/2.02  fof(f51,plain,(
% 11.75/2.02    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/2.02    inference(cnf_transformation,[],[f25])).
% 11.75/2.02  
% 11.75/2.02  fof(f43,plain,(
% 11.75/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.75/2.02    inference(cnf_transformation,[],[f30])).
% 11.75/2.02  
% 11.75/2.02  fof(f1,axiom,(
% 11.75/2.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f14,plain,(
% 11.75/2.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.75/2.02    inference(ennf_transformation,[],[f1])).
% 11.75/2.02  
% 11.75/2.02  fof(f15,plain,(
% 11.75/2.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.75/2.02    inference(flattening,[],[f14])).
% 11.75/2.02  
% 11.75/2.02  fof(f39,plain,(
% 11.75/2.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.75/2.02    inference(cnf_transformation,[],[f15])).
% 11.75/2.02  
% 11.75/2.02  fof(f6,axiom,(
% 11.75/2.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f19,plain,(
% 11.75/2.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/2.02    inference(ennf_transformation,[],[f6])).
% 11.75/2.02  
% 11.75/2.02  fof(f20,plain,(
% 11.75/2.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/2.02    inference(flattening,[],[f19])).
% 11.75/2.02  
% 11.75/2.02  fof(f45,plain,(
% 11.75/2.02    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/2.02    inference(cnf_transformation,[],[f20])).
% 11.75/2.02  
% 11.75/2.02  fof(f9,axiom,(
% 11.75/2.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f24,plain,(
% 11.75/2.02    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/2.02    inference(ennf_transformation,[],[f9])).
% 11.75/2.02  
% 11.75/2.02  fof(f31,plain,(
% 11.75/2.02    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/2.02    inference(nnf_transformation,[],[f24])).
% 11.75/2.02  
% 11.75/2.02  fof(f49,plain,(
% 11.75/2.02    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/2.02    inference(cnf_transformation,[],[f31])).
% 11.75/2.02  
% 11.75/2.02  fof(f2,axiom,(
% 11.75/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f16,plain,(
% 11.75/2.02    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.75/2.02    inference(ennf_transformation,[],[f2])).
% 11.75/2.02  
% 11.75/2.02  fof(f40,plain,(
% 11.75/2.02    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.75/2.02    inference(cnf_transformation,[],[f16])).
% 11.75/2.02  
% 11.75/2.02  fof(f58,plain,(
% 11.75/2.02    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 11.75/2.02    inference(cnf_transformation,[],[f38])).
% 11.75/2.02  
% 11.75/2.02  fof(f57,plain,(
% 11.75/2.02    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 11.75/2.02    inference(cnf_transformation,[],[f38])).
% 11.75/2.02  
% 11.75/2.02  fof(f7,axiom,(
% 11.75/2.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f21,plain,(
% 11.75/2.02    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/2.02    inference(ennf_transformation,[],[f7])).
% 11.75/2.02  
% 11.75/2.02  fof(f47,plain,(
% 11.75/2.02    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/2.02    inference(cnf_transformation,[],[f21])).
% 11.75/2.02  
% 11.75/2.02  fof(f3,axiom,(
% 11.75/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f17,plain,(
% 11.75/2.02    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.75/2.02    inference(ennf_transformation,[],[f3])).
% 11.75/2.02  
% 11.75/2.02  fof(f41,plain,(
% 11.75/2.02    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.75/2.02    inference(cnf_transformation,[],[f17])).
% 11.75/2.02  
% 11.75/2.02  fof(f11,axiom,(
% 11.75/2.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f26,plain,(
% 11.75/2.02    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/2.02    inference(ennf_transformation,[],[f11])).
% 11.75/2.02  
% 11.75/2.02  fof(f27,plain,(
% 11.75/2.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/2.02    inference(flattening,[],[f26])).
% 11.75/2.02  
% 11.75/2.02  fof(f52,plain,(
% 11.75/2.02    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/2.02    inference(cnf_transformation,[],[f27])).
% 11.75/2.02  
% 11.75/2.02  fof(f59,plain,(
% 11.75/2.02    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 11.75/2.02    inference(cnf_transformation,[],[f38])).
% 11.75/2.02  
% 11.75/2.02  fof(f4,axiom,(
% 11.75/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 11.75/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.75/2.02  
% 11.75/2.02  fof(f18,plain,(
% 11.75/2.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.75/2.02    inference(ennf_transformation,[],[f4])).
% 11.75/2.02  
% 11.75/2.02  fof(f42,plain,(
% 11.75/2.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.75/2.02    inference(cnf_transformation,[],[f18])).
% 11.75/2.02  
% 11.75/2.02  cnf(c_4,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.75/2.02      inference(cnf_transformation,[],[f44]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1337,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.75/2.02      | r1_tarski(X0,X1) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_18,negated_conjecture,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 11.75/2.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.75/2.02      inference(cnf_transformation,[],[f56]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1331,plain,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 11.75/2.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_14,negated_conjecture,
% 11.75/2.02      ( ~ v3_pre_topc(X0,sK0)
% 11.75/2.02      | ~ r2_hidden(sK1,X0)
% 11.75/2.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ r1_tarski(X0,sK2) ),
% 11.75/2.02      inference(cnf_transformation,[],[f60]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1335,plain,
% 11.75/2.02      ( v3_pre_topc(X0,sK0) != iProver_top
% 11.75/2.02      | r2_hidden(sK1,X0) != iProver_top
% 11.75/2.02      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 11.75/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(X0,sK2) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1539,plain,
% 11.75/2.02      ( v3_pre_topc(X0,sK0) != iProver_top
% 11.75/2.02      | r2_hidden(sK1,X0) != iProver_top
% 11.75/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.75/2.02      | r1_tarski(X0,sK2) != iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_1331,c_1335]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_19,negated_conjecture,
% 11.75/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.75/2.02      inference(cnf_transformation,[],[f55]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_24,plain,
% 11.75/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_25,plain,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 11.75/2.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_9,plain,
% 11.75/2.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.75/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.75/2.02      | ~ l1_pre_topc(X0)
% 11.75/2.02      | ~ v2_pre_topc(X0) ),
% 11.75/2.02      inference(cnf_transformation,[],[f48]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_21,negated_conjecture,
% 11.75/2.02      ( v2_pre_topc(sK0) ),
% 11.75/2.02      inference(cnf_transformation,[],[f53]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_303,plain,
% 11.75/2.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.75/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.75/2.02      | ~ l1_pre_topc(X0)
% 11.75/2.02      | sK0 != X0 ),
% 11.75/2.02      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_304,plain,
% 11.75/2.02      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ l1_pre_topc(sK0) ),
% 11.75/2.02      inference(unflattening,[status(thm)],[c_303]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_20,negated_conjecture,
% 11.75/2.02      ( l1_pre_topc(sK0) ),
% 11.75/2.02      inference(cnf_transformation,[],[f54]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_308,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 11.75/2.02      inference(global_propositional_subsumption,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_304,c_20]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_309,plain,
% 11.75/2.02      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.75/2.02      inference(renaming,[status(thm)],[c_308]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1373,plain,
% 11.75/2.02      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 11.75/2.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_309]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1374,plain,
% 11.75/2.02      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0) = iProver_top
% 11.75/2.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1373]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_12,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.75/2.02      | ~ l1_pre_topc(X1) ),
% 11.75/2.02      inference(cnf_transformation,[],[f51]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_367,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.75/2.02      | sK0 != X1 ),
% 11.75/2.02      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_368,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 11.75/2.02      inference(unflattening,[status(thm)],[c_367]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1391,plain,
% 11.75/2.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_368]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1392,plain,
% 11.75/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1437,plain,
% 11.75/2.02      ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 11.75/2.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 11.75/2.02      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_14]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1438,plain,
% 11.75/2.02      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0) != iProver_top
% 11.75/2.02      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 11.75/2.02      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1437]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_5,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.75/2.02      inference(cnf_transformation,[],[f43]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1454,plain,
% 11.75/2.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,X0) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_5]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1546,plain,
% 11.75/2.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_1454]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1547,plain,
% 11.75/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1546]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_0,plain,
% 11.75/2.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 11.75/2.02      inference(cnf_transformation,[],[f39]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1483,plain,
% 11.75/2.02      ( ~ r1_tarski(X0,X1)
% 11.75/2.02      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 11.75/2.02      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_0]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1627,plain,
% 11.75/2.02      ( r1_tarski(X0,u1_struct_0(sK0))
% 11.75/2.02      | ~ r1_tarski(X0,sK2)
% 11.75/2.02      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_1483]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1826,plain,
% 11.75/2.02      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 11.75/2.02      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 11.75/2.02      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_1627]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1827,plain,
% 11.75/2.02      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 11.75/2.02      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1826]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1376,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_4]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1959,plain,
% 11.75/2.02      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_1376]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1960,plain,
% 11.75/2.02      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1959]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2641,plain,
% 11.75/2.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.75/2.02      inference(global_propositional_subsumption,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_1539,c_24,c_25,c_1374,c_1392,c_1438,c_1547,c_1827,
% 11.75/2.02                 c_1960]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_7,plain,
% 11.75/2.02      ( ~ v4_pre_topc(X0,X1)
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | ~ l1_pre_topc(X1)
% 11.75/2.02      | k2_pre_topc(X1,X0) = X0 ),
% 11.75/2.02      inference(cnf_transformation,[],[f45]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_421,plain,
% 11.75/2.02      ( ~ v4_pre_topc(X0,X1)
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | k2_pre_topc(X1,X0) = X0
% 11.75/2.02      | sK0 != X1 ),
% 11.75/2.02      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_422,plain,
% 11.75/2.02      ( ~ v4_pre_topc(X0,sK0)
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | k2_pre_topc(sK0,X0) = X0 ),
% 11.75/2.02      inference(unflattening,[status(thm)],[c_421]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_11,plain,
% 11.75/2.02      ( ~ v3_pre_topc(X0,X1)
% 11.75/2.02      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | ~ l1_pre_topc(X1) ),
% 11.75/2.02      inference(cnf_transformation,[],[f49]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_379,plain,
% 11.75/2.02      ( ~ v3_pre_topc(X0,X1)
% 11.75/2.02      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | sK0 != X1 ),
% 11.75/2.02      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_380,plain,
% 11.75/2.02      ( ~ v3_pre_topc(X0,sK0)
% 11.75/2.02      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.75/2.02      inference(unflattening,[status(thm)],[c_379]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_479,plain,
% 11.75/2.02      ( ~ v3_pre_topc(X0,sK0)
% 11.75/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | k2_pre_topc(sK0,X1) = X1
% 11.75/2.02      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 11.75/2.02      | sK0 != sK0 ),
% 11.75/2.02      inference(resolution_lifted,[status(thm)],[c_422,c_380]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_480,plain,
% 11.75/2.02      ( ~ v3_pre_topc(X0,sK0)
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
% 11.75/2.02      inference(unflattening,[status(thm)],[c_479]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1322,plain,
% 11.75/2.02      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 11.75/2.02      | v3_pre_topc(X0,sK0) != iProver_top
% 11.75/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_481,plain,
% 11.75/2.02      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 11.75/2.02      | v3_pre_topc(X0,sK0) != iProver_top
% 11.75/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1486,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_5]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1487,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(X0,u1_struct_0(sK0)) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.75/2.02      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 11.75/2.02      inference(cnf_transformation,[],[f40]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_168,plain,
% 11.75/2.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.75/2.02      inference(prop_impl,[status(thm)],[c_4]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_169,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.75/2.02      inference(renaming,[status(thm)],[c_168]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_214,plain,
% 11.75/2.02      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 11.75/2.02      | ~ r1_tarski(X1,X0) ),
% 11.75/2.02      inference(bin_hyper_res,[status(thm)],[c_1,c_169]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1497,plain,
% 11.75/2.02      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_214]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1498,plain,
% 11.75/2.02      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.75/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1497]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1693,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | v3_pre_topc(X0,sK0) != iProver_top
% 11.75/2.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
% 11.75/2.02      inference(global_propositional_subsumption,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_1322,c_481,c_1487,c_1498]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1694,plain,
% 11.75/2.02      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 11.75/2.02      | v3_pre_topc(X0,sK0) != iProver_top
% 11.75/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.75/2.02      inference(renaming,[status(thm)],[c_1693]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2649,plain,
% 11.75/2.02      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
% 11.75/2.02      | v3_pre_topc(sK3,sK0) != iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_2641,c_1694]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_16,negated_conjecture,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(sK3,sK2) ),
% 11.75/2.02      inference(cnf_transformation,[],[f58]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_17,negated_conjecture,
% 11.75/2.02      ( v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 11.75/2.02      inference(cnf_transformation,[],[f57]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_531,plain,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 11.75/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 11.75/2.02      | sK3 != X0
% 11.75/2.02      | sK0 != sK0 ),
% 11.75/2.02      inference(resolution_lifted,[status(thm)],[c_480,c_17]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_532,plain,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 11.75/2.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 11.75/2.02      inference(unflattening,[status(thm)],[c_531]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_534,plain,
% 11.75/2.02      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 11.75/2.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 11.75/2.02      inference(global_propositional_subsumption,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_532,c_18]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_535,plain,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 11.75/2.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 11.75/2.02      inference(renaming,[status(thm)],[c_534]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1797,plain,
% 11.75/2.02      ( ~ r1_tarski(X0,X1)
% 11.75/2.02      | ~ r1_tarski(X1,u1_struct_0(X2))
% 11.75/2.02      | r1_tarski(X0,u1_struct_0(X2)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_0]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2374,plain,
% 11.75/2.02      ( r1_tarski(sK3,u1_struct_0(X0))
% 11.75/2.02      | ~ r1_tarski(sK3,sK2)
% 11.75/2.02      | ~ r1_tarski(sK2,u1_struct_0(X0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_1797]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2376,plain,
% 11.75/2.02      ( r1_tarski(sK3,u1_struct_0(sK0))
% 11.75/2.02      | ~ r1_tarski(sK3,sK2)
% 11.75/2.02      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_2374]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2568,plain,
% 11.75/2.02      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ r1_tarski(sK3,u1_struct_0(sK0)) ),
% 11.75/2.02      inference(instantiation,[status(thm)],[c_1497]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_3499,plain,
% 11.75/2.02      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 11.75/2.02      inference(global_propositional_subsumption,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_2649,c_19,c_16,c_535,c_1373,c_1391,c_1437,c_1546,
% 11.75/2.02                 c_1826,c_1959,c_2376,c_2568]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_8,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | ~ l1_pre_topc(X1)
% 11.75/2.02      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 11.75/2.02      inference(cnf_transformation,[],[f47]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_409,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 11.75/2.02      | sK0 != X1 ),
% 11.75/2.02      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_410,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 11.75/2.02      inference(unflattening,[status(thm)],[c_409]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1324,plain,
% 11.75/2.02      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 11.75/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2647,plain,
% 11.75/2.02      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_2641,c_1324]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_3501,plain,
% 11.75/2.02      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
% 11.75/2.02      inference(demodulation,[status(thm)],[c_3499,c_2647]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1336,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.75/2.02      | r1_tarski(X0,X1) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2645,plain,
% 11.75/2.02      ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_2641,c_1336]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.75/2.02      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 11.75/2.02      inference(cnf_transformation,[],[f41]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_215,plain,
% 11.75/2.02      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 11.75/2.02      inference(bin_hyper_res,[status(thm)],[c_2,c_169]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1328,plain,
% 11.75/2.02      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 11.75/2.02      | r1_tarski(X1,X0) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2741,plain,
% 11.75/2.02      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_2645,c_1328]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_3502,plain,
% 11.75/2.02      ( k1_tops_1(sK0,sK3) = sK3 ),
% 11.75/2.02      inference(light_normalisation,[status(thm)],[c_3501,c_2741]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_13,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | ~ r1_tarski(X0,X2)
% 11.75/2.02      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.75/2.02      | ~ l1_pre_topc(X1) ),
% 11.75/2.02      inference(cnf_transformation,[],[f52]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_349,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.02      | ~ r1_tarski(X0,X2)
% 11.75/2.02      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.75/2.02      | sK0 != X1 ),
% 11.75/2.02      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_350,plain,
% 11.75/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/2.02      | ~ r1_tarski(X0,X1)
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 11.75/2.02      inference(unflattening,[status(thm)],[c_349]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1326,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(X0,X1) != iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_36696,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(sK3,X0) != iProver_top
% 11.75/2.02      | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_3502,c_1326]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_37345,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(sK3,X0) != iProver_top
% 11.75/2.02      | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
% 11.75/2.02      inference(global_propositional_subsumption,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_36696,c_24,c_25,c_1374,c_1392,c_1438,c_1547,c_1827,
% 11.75/2.02                 c_1960]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_37351,plain,
% 11.75/2.02      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.75/2.02      | r1_tarski(sK3,X0) != iProver_top
% 11.75/2.02      | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_1337,c_37345]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1330,plain,
% 11.75/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1339,plain,
% 11.75/2.02      ( r1_tarski(X0,X1) != iProver_top
% 11.75/2.02      | r1_tarski(X2,X0) != iProver_top
% 11.75/2.02      | r1_tarski(X2,X1) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2200,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(X0,X1) != iProver_top
% 11.75/2.02      | r1_tarski(X2,k1_tops_1(sK0,X0)) != iProver_top
% 11.75/2.02      | r1_tarski(X2,k1_tops_1(sK0,X1)) = iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_1326,c_1339]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_4352,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(X1,X0) != iProver_top
% 11.75/2.02      | r1_tarski(X2,k1_tops_1(sK0,X1)) != iProver_top
% 11.75/2.02      | r1_tarski(X2,k1_tops_1(sK0,X0)) = iProver_top
% 11.75/2.02      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_1337,c_2200]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_7189,plain,
% 11.75/2.02      ( r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
% 11.75/2.02      | r1_tarski(X0,k1_tops_1(sK0,sK2)) = iProver_top
% 11.75/2.02      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 11.75/2.02      | r1_tarski(X1,sK2) != iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_1330,c_4352]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_38575,plain,
% 11.75/2.02      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.75/2.02      | r1_tarski(X0,sK2) != iProver_top
% 11.75/2.02      | r1_tarski(sK3,X0) != iProver_top
% 11.75/2.02      | r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_37351,c_7189]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_27,plain,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 11.75/2.02      | r1_tarski(sK3,sK2) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1325,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2650,plain,
% 11.75/2.02      ( r1_tarski(k1_tops_1(sK0,sK3),sK3) = iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_2641,c_1325]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_7415,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(X0,X1) != iProver_top
% 11.75/2.02      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 11.75/2.02      | r1_tarski(X1,sK2) != iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_1326,c_7189]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1377,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.75/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1376]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1484,plain,
% 11.75/2.02      ( r1_tarski(X0,X1) != iProver_top
% 11.75/2.02      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 11.75/2.02      | r1_tarski(X0,u1_struct_0(sK0)) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_23917,plain,
% 11.75/2.02      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(X0,X1) != iProver_top
% 11.75/2.02      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 11.75/2.02      | r1_tarski(X1,sK2) != iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = iProver_top ),
% 11.75/2.02      inference(global_propositional_subsumption,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_7415,c_1377,c_1484]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_23918,plain,
% 11.75/2.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(X1,X0) != iProver_top
% 11.75/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.75/2.02      | r1_tarski(X0,sK2) != iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK2)) = iProver_top ),
% 11.75/2.02      inference(renaming,[status(thm)],[c_23917]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1628,plain,
% 11.75/2.02      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 11.75/2.02      | r1_tarski(X0,sK2) != iProver_top
% 11.75/2.02      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_1627]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_23921,plain,
% 11.75/2.02      ( r1_tarski(X1,X0) != iProver_top
% 11.75/2.02      | r1_tarski(X0,sK2) != iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK2)) = iProver_top ),
% 11.75/2.02      inference(global_propositional_subsumption,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_23918,c_24,c_1377,c_1547,c_1628]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_23922,plain,
% 11.75/2.02      ( r1_tarski(X0,X1) != iProver_top
% 11.75/2.02      | r1_tarski(X1,sK2) != iProver_top
% 11.75/2.02      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = iProver_top ),
% 11.75/2.02      inference(renaming,[status(thm)],[c_23921]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_23944,plain,
% 11.75/2.02      ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK3)),k1_tops_1(sK0,sK2)) = iProver_top
% 11.75/2.02      | r1_tarski(sK3,sK2) != iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_2650,c_23922]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_23972,plain,
% 11.75/2.02      ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top
% 11.75/2.02      | r1_tarski(sK3,sK2) != iProver_top ),
% 11.75/2.02      inference(light_normalisation,[status(thm)],[c_23944,c_3502]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_38876,plain,
% 11.75/2.02      ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top ),
% 11.75/2.02      inference(global_propositional_subsumption,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_38575,c_24,c_27,c_1374,c_1392,c_1438,c_1547,c_1827,
% 11.75/2.02                 c_1960,c_23972]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_15,negated_conjecture,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r2_hidden(sK1,sK3) ),
% 11.75/2.02      inference(cnf_transformation,[],[f59]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1334,plain,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 11.75/2.02      | r2_hidden(sK1,sK3) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1534,plain,
% 11.75/2.02      ( v3_pre_topc(X0,sK0) != iProver_top
% 11.75/2.02      | r2_hidden(sK1,X0) != iProver_top
% 11.75/2.02      | r2_hidden(sK1,sK3) = iProver_top
% 11.75/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/2.02      | r1_tarski(X0,sK2) != iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_1334,c_1335]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_28,plain,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 11.75/2.02      | r2_hidden(sK1,sK3) = iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_2636,plain,
% 11.75/2.02      ( r2_hidden(sK1,sK3) = iProver_top ),
% 11.75/2.02      inference(global_propositional_subsumption,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_1534,c_24,c_28,c_1374,c_1392,c_1438,c_1547,c_1827,
% 11.75/2.02                 c_1960]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_3,plain,
% 11.75/2.02      ( ~ r2_hidden(X0,X1)
% 11.75/2.02      | r2_hidden(X0,X2)
% 11.75/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 11.75/2.02      inference(cnf_transformation,[],[f42]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1338,plain,
% 11.75/2.02      ( r2_hidden(X0,X1) != iProver_top
% 11.75/2.02      | r2_hidden(X0,X2) = iProver_top
% 11.75/2.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 11.75/2.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_1860,plain,
% 11.75/2.02      ( r2_hidden(X0,X1) != iProver_top
% 11.75/2.02      | r2_hidden(X0,X2) = iProver_top
% 11.75/2.02      | r1_tarski(X1,X2) != iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_1337,c_1338]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_3591,plain,
% 11.75/2.02      ( r2_hidden(sK1,X0) = iProver_top
% 11.75/2.02      | r1_tarski(sK3,X0) != iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_2636,c_1860]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(c_38912,plain,
% 11.75/2.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 11.75/2.02      inference(superposition,[status(thm)],[c_38876,c_3591]) ).
% 11.75/2.02  
% 11.75/2.02  cnf(contradiction,plain,
% 11.75/2.02      ( $false ),
% 11.75/2.02      inference(minisat,
% 11.75/2.02                [status(thm)],
% 11.75/2.02                [c_38912,c_1960,c_1827,c_1547,c_1438,c_1392,c_1374,c_24]) ).
% 11.75/2.02  
% 11.75/2.02  
% 11.75/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.75/2.02  
% 11.75/2.02  ------                               Statistics
% 11.75/2.02  
% 11.75/2.02  ------ General
% 11.75/2.02  
% 11.75/2.02  abstr_ref_over_cycles:                  0
% 11.75/2.02  abstr_ref_under_cycles:                 0
% 11.75/2.02  gc_basic_clause_elim:                   0
% 11.75/2.02  forced_gc_time:                         0
% 11.75/2.02  parsing_time:                           0.008
% 11.75/2.02  unif_index_cands_time:                  0.
% 11.75/2.02  unif_index_add_time:                    0.
% 11.75/2.02  orderings_time:                         0.
% 11.75/2.02  out_proof_time:                         0.017
% 11.75/2.02  total_time:                             1.293
% 11.75/2.02  num_of_symbols:                         47
% 11.75/2.02  num_of_terms:                           25367
% 11.75/2.02  
% 11.75/2.02  ------ Preprocessing
% 11.75/2.02  
% 11.75/2.02  num_of_splits:                          0
% 11.75/2.02  num_of_split_atoms:                     0
% 11.75/2.02  num_of_reused_defs:                     0
% 11.75/2.02  num_eq_ax_congr_red:                    2
% 11.75/2.02  num_of_sem_filtered_clauses:            1
% 11.75/2.02  num_of_subtypes:                        0
% 11.75/2.02  monotx_restored_types:                  0
% 11.75/2.02  sat_num_of_epr_types:                   0
% 11.75/2.02  sat_num_of_non_cyclic_types:            0
% 11.75/2.02  sat_guarded_non_collapsed_types:        0
% 11.75/2.02  num_pure_diseq_elim:                    0
% 11.75/2.02  simp_replaced_by:                       0
% 11.75/2.02  res_preprocessed:                       99
% 11.75/2.02  prep_upred:                             0
% 11.75/2.02  prep_unflattend:                        18
% 11.75/2.02  smt_new_axioms:                         0
% 11.75/2.02  pred_elim_cands:                        4
% 11.75/2.02  pred_elim:                              3
% 11.75/2.02  pred_elim_cl:                           4
% 11.75/2.02  pred_elim_cycles:                       5
% 11.75/2.02  merged_defs:                            8
% 11.75/2.02  merged_defs_ncl:                        0
% 11.75/2.02  bin_hyper_res:                          10
% 11.75/2.02  prep_cycles:                            4
% 11.75/2.02  pred_elim_time:                         0.009
% 11.75/2.02  splitting_time:                         0.
% 11.75/2.02  sem_filter_time:                        0.
% 11.75/2.02  monotx_time:                            0.
% 11.75/2.02  subtype_inf_time:                       0.
% 11.75/2.02  
% 11.75/2.02  ------ Problem properties
% 11.75/2.02  
% 11.75/2.02  clauses:                                18
% 11.75/2.02  conjectures:                            6
% 11.75/2.02  epr:                                    1
% 11.75/2.02  horn:                                   14
% 11.75/2.02  ground:                                 5
% 11.75/2.02  unary:                                  1
% 11.75/2.02  binary:                                 11
% 11.75/2.02  lits:                                   46
% 11.75/2.02  lits_eq:                                4
% 11.75/2.02  fd_pure:                                0
% 11.75/2.02  fd_pseudo:                              0
% 11.75/2.02  fd_cond:                                0
% 11.75/2.02  fd_pseudo_cond:                         0
% 11.75/2.02  ac_symbols:                             0
% 11.75/2.02  
% 11.75/2.02  ------ Propositional Solver
% 11.75/2.02  
% 11.75/2.02  prop_solver_calls:                      36
% 11.75/2.02  prop_fast_solver_calls:                 2251
% 11.75/2.02  smt_solver_calls:                       0
% 11.75/2.02  smt_fast_solver_calls:                  0
% 11.75/2.02  prop_num_of_clauses:                    18905
% 11.75/2.02  prop_preprocess_simplified:             35568
% 11.75/2.02  prop_fo_subsumed:                       188
% 11.75/2.02  prop_solver_time:                       0.
% 11.75/2.02  smt_solver_time:                        0.
% 11.75/2.02  smt_fast_solver_time:                   0.
% 11.75/2.02  prop_fast_solver_time:                  0.
% 11.75/2.02  prop_unsat_core_time:                   0.002
% 11.75/2.02  
% 11.75/2.02  ------ QBF
% 11.75/2.02  
% 11.75/2.02  qbf_q_res:                              0
% 11.75/2.02  qbf_num_tautologies:                    0
% 11.75/2.02  qbf_prep_cycles:                        0
% 11.75/2.02  
% 11.75/2.02  ------ BMC1
% 11.75/2.02  
% 11.75/2.02  bmc1_current_bound:                     -1
% 11.75/2.02  bmc1_last_solved_bound:                 -1
% 11.75/2.02  bmc1_unsat_core_size:                   -1
% 11.75/2.02  bmc1_unsat_core_parents_size:           -1
% 11.75/2.02  bmc1_merge_next_fun:                    0
% 11.75/2.02  bmc1_unsat_core_clauses_time:           0.
% 11.75/2.02  
% 11.75/2.02  ------ Instantiation
% 11.75/2.02  
% 11.75/2.02  inst_num_of_clauses:                    4771
% 11.75/2.02  inst_num_in_passive:                    2279
% 11.75/2.02  inst_num_in_active:                     1593
% 11.75/2.02  inst_num_in_unprocessed:                899
% 11.75/2.02  inst_num_of_loops:                      1700
% 11.75/2.02  inst_num_of_learning_restarts:          0
% 11.75/2.02  inst_num_moves_active_passive:          102
% 11.75/2.02  inst_lit_activity:                      0
% 11.75/2.02  inst_lit_activity_moves:                2
% 11.75/2.02  inst_num_tautologies:                   0
% 11.75/2.02  inst_num_prop_implied:                  0
% 11.75/2.02  inst_num_existing_simplified:           0
% 11.75/2.02  inst_num_eq_res_simplified:             0
% 11.75/2.02  inst_num_child_elim:                    0
% 11.75/2.02  inst_num_of_dismatching_blockings:      1665
% 11.75/2.02  inst_num_of_non_proper_insts:           4685
% 11.75/2.02  inst_num_of_duplicates:                 0
% 11.75/2.02  inst_inst_num_from_inst_to_res:         0
% 11.75/2.02  inst_dismatching_checking_time:         0.
% 11.75/2.02  
% 11.75/2.02  ------ Resolution
% 11.75/2.02  
% 11.75/2.02  res_num_of_clauses:                     0
% 11.75/2.02  res_num_in_passive:                     0
% 11.75/2.02  res_num_in_active:                      0
% 11.75/2.02  res_num_of_loops:                       103
% 11.75/2.02  res_forward_subset_subsumed:            74
% 11.75/2.02  res_backward_subset_subsumed:           0
% 11.75/2.02  res_forward_subsumed:                   0
% 11.75/2.02  res_backward_subsumed:                  0
% 11.75/2.02  res_forward_subsumption_resolution:     0
% 11.75/2.02  res_backward_subsumption_resolution:    0
% 11.75/2.02  res_clause_to_clause_subsumption:       28234
% 11.75/2.02  res_orphan_elimination:                 0
% 11.75/2.02  res_tautology_del:                      348
% 11.75/2.02  res_num_eq_res_simplified:              0
% 11.75/2.02  res_num_sel_changes:                    0
% 11.75/2.02  res_moves_from_active_to_pass:          0
% 11.75/2.02  
% 11.75/2.02  ------ Superposition
% 11.75/2.02  
% 11.75/2.02  sup_time_total:                         0.
% 11.75/2.02  sup_time_generating:                    0.
% 11.75/2.02  sup_time_sim_full:                      0.
% 11.75/2.02  sup_time_sim_immed:                     0.
% 11.75/2.02  
% 11.75/2.02  sup_num_of_clauses:                     1669
% 11.75/2.02  sup_num_in_active:                      278
% 11.75/2.02  sup_num_in_passive:                     1391
% 11.75/2.02  sup_num_of_loops:                       338
% 11.75/2.02  sup_fw_superposition:                   2526
% 11.75/2.02  sup_bw_superposition:                   2005
% 11.75/2.02  sup_immediate_simplified:               2036
% 11.75/2.02  sup_given_eliminated:                   1
% 11.75/2.02  comparisons_done:                       0
% 11.75/2.02  comparisons_avoided:                    0
% 11.75/2.02  
% 11.75/2.02  ------ Simplifications
% 11.75/2.02  
% 11.75/2.02  
% 11.75/2.02  sim_fw_subset_subsumed:                 1098
% 11.75/2.02  sim_bw_subset_subsumed:                 289
% 11.75/2.02  sim_fw_subsumed:                        615
% 11.75/2.02  sim_bw_subsumed:                        84
% 11.75/2.02  sim_fw_subsumption_res:                 0
% 11.75/2.02  sim_bw_subsumption_res:                 0
% 11.75/2.02  sim_tautology_del:                      108
% 11.75/2.02  sim_eq_tautology_del:                   51
% 11.75/2.02  sim_eq_res_simp:                        0
% 11.75/2.02  sim_fw_demodulated:                     2
% 11.75/2.02  sim_bw_demodulated:                     27
% 11.75/2.02  sim_light_normalised:                   318
% 11.75/2.02  sim_joinable_taut:                      0
% 11.75/2.02  sim_joinable_simp:                      0
% 11.75/2.02  sim_ac_normalised:                      0
% 11.75/2.02  sim_smt_subsumption:                    0
% 11.75/2.02  
%------------------------------------------------------------------------------
