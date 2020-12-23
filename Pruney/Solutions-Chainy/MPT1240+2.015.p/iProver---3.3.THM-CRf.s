%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:00 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  143 (1116 expanded)
%              Number of clauses        :   82 ( 263 expanded)
%              Number of leaves         :   16 ( 278 expanded)
%              Depth                    :   28
%              Number of atoms          :  507 (9750 expanded)
%              Number of equality atoms :  103 ( 192 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f30])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f39,f38,f37])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1254,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_445,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_446,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_391,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_392,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_508,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) = X1
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_446,c_392])).

cnf(c_509,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_521,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_509,c_4])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | sK3 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_521,c_18])).

cnf(c_558,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_560,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_19])).

cnf(c_1248,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_1390,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(X0,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_315,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_316,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_21])).

cnf(c_321,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_320])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(X0,sK2)
    | k1_tops_1(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_321])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_422])).

cnf(c_1396,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_2281,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1248,c_20,c_560,c_1390,c_1396])).

cnf(c_1255,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1391,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1390])).

cnf(c_1397,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_1434,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1255,c_25,c_26,c_1391,c_1397])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_1250,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_2063,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_1434,c_1250])).

cnf(c_2284,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_2281,c_2063])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1258,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2392,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1434,c_1258])).

cnf(c_3016,plain,
    ( k1_tops_1(sK0,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2284,c_2392])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_1253,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_3027,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3016,c_1253])).

cnf(c_8591,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3027,c_25,c_26,c_1391,c_1397])).

cnf(c_8602,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_8591])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8651,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8602,c_25,c_28,c_1391,c_1397])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1257,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_29,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1428,plain,
    ( r2_hidden(sK1,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1257,c_25,c_29,c_1391,c_1397])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1261,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1262,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1771,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1262])).

cnf(c_3268,plain,
    ( k2_xboole_0(k1_tarski(sK1),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1428,c_1771])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1263,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4193,plain,
    ( r1_tarski(k1_tarski(sK1),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3268,c_1263])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1260,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4201,plain,
    ( r2_hidden(sK1,X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4193,c_1260])).

cnf(c_8658,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8651,c_4201])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8658,c_1397,c_1391,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.32/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.99  
% 3.32/0.99  ------  iProver source info
% 3.32/0.99  
% 3.32/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.99  git: non_committed_changes: false
% 3.32/0.99  git: last_make_outside_of_git: false
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    --mode clausify
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         false
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     num_symb
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       true
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     false
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   []
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_full_bw                           [BwDemod]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  ------ Parsing...
% 3.32/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.99  ------ Proving...
% 3.32/0.99  ------ Problem Properties 
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  clauses                                 18
% 3.32/0.99  conjectures                             4
% 3.32/0.99  EPR                                     0
% 3.32/0.99  Horn                                    14
% 3.32/0.99  unary                                   1
% 3.32/0.99  binary                                  14
% 3.32/0.99  lits                                    42
% 3.32/0.99  lits eq                                 6
% 3.32/0.99  fd_pure                                 0
% 3.32/0.99  fd_pseudo                               0
% 3.32/0.99  fd_cond                                 0
% 3.32/0.99  fd_pseudo_cond                          0
% 3.32/0.99  AC symbols                              0
% 3.32/0.99  
% 3.32/0.99  ------ Schedule dynamic 5 is on 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  Current options:
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    --mode clausify
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         false
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     none
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       false
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     false
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   []
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_full_bw                           [BwDemod]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ Proving...
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  % SZS status Theorem for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  fof(f13,conjecture,(
% 3.32/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f14,negated_conjecture,(
% 3.32/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.32/0.99    inference(negated_conjecture,[],[f13])).
% 3.32/0.99  
% 3.32/0.99  fof(f30,plain,(
% 3.32/0.99    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f14])).
% 3.32/0.99  
% 3.32/0.99  fof(f31,plain,(
% 3.32/0.99    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.32/0.99    inference(flattening,[],[f30])).
% 3.32/0.99  
% 3.32/0.99  fof(f34,plain,(
% 3.32/0.99    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.32/0.99    inference(nnf_transformation,[],[f31])).
% 3.32/0.99  
% 3.32/0.99  fof(f35,plain,(
% 3.32/0.99    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.32/0.99    inference(flattening,[],[f34])).
% 3.32/0.99  
% 3.32/0.99  fof(f36,plain,(
% 3.32/0.99    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.32/0.99    inference(rectify,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f39,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3) & r1_tarski(sK3,X2) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f38,plain,(
% 3.32/0.99    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK1,k1_tops_1(X0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK1,k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f37,plain,(
% 3.32/0.99    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f40,plain,(
% 3.32/0.99    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f39,f38,f37])).
% 3.32/0.99  
% 3.32/0.99  fof(f58,plain,(
% 3.32/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.32/0.99    inference(cnf_transformation,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f6,axiom,(
% 3.32/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f19,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f6])).
% 3.32/0.99  
% 3.32/0.99  fof(f20,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/0.99    inference(flattening,[],[f19])).
% 3.32/0.99  
% 3.32/0.99  fof(f47,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f20])).
% 3.32/0.99  
% 3.32/0.99  fof(f57,plain,(
% 3.32/0.99    l1_pre_topc(sK0)),
% 3.32/0.99    inference(cnf_transformation,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f10,axiom,(
% 3.32/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f26,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f10])).
% 3.32/0.99  
% 3.32/0.99  fof(f33,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/0.99    inference(nnf_transformation,[],[f26])).
% 3.32/0.99  
% 3.32/0.99  fof(f52,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f33])).
% 3.32/0.99  
% 3.32/0.99  fof(f4,axiom,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f17,plain,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f4])).
% 3.32/0.99  
% 3.32/0.99  fof(f45,plain,(
% 3.32/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f17])).
% 3.32/0.99  
% 3.32/0.99  fof(f60,plain,(
% 3.32/0.99    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.32/0.99    inference(cnf_transformation,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f59,plain,(
% 3.32/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.32/0.99    inference(cnf_transformation,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f11,axiom,(
% 3.32/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f27,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f11])).
% 3.32/0.99  
% 3.32/0.99  fof(f54,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f27])).
% 3.32/0.99  
% 3.32/0.99  fof(f63,plain,(
% 3.32/0.99    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f9,axiom,(
% 3.32/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f24,plain,(
% 3.32/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f9])).
% 3.32/0.99  
% 3.32/0.99  fof(f25,plain,(
% 3.32/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.32/0.99    inference(flattening,[],[f24])).
% 3.32/0.99  
% 3.32/0.99  fof(f51,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f25])).
% 3.32/0.99  
% 3.32/0.99  fof(f56,plain,(
% 3.32/0.99    v2_pre_topc(sK0)),
% 3.32/0.99    inference(cnf_transformation,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f8,axiom,(
% 3.32/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f22,plain,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f8])).
% 3.32/0.99  
% 3.32/0.99  fof(f23,plain,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.32/0.99    inference(flattening,[],[f22])).
% 3.32/0.99  
% 3.32/0.99  fof(f50,plain,(
% 3.32/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f23])).
% 3.32/0.99  
% 3.32/0.99  fof(f7,axiom,(
% 3.32/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f21,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f7])).
% 3.32/0.99  
% 3.32/0.99  fof(f49,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f21])).
% 3.32/0.99  
% 3.32/0.99  fof(f5,axiom,(
% 3.32/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f18,plain,(
% 3.32/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f5])).
% 3.32/0.99  
% 3.32/0.99  fof(f46,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f18])).
% 3.32/0.99  
% 3.32/0.99  fof(f12,axiom,(
% 3.32/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f28,plain,(
% 3.32/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.00    inference(ennf_transformation,[],[f12])).
% 3.32/1.00  
% 3.32/1.00  fof(f29,plain,(
% 3.32/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.00    inference(flattening,[],[f28])).
% 3.32/1.00  
% 3.32/1.00  fof(f55,plain,(
% 3.32/1.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f29])).
% 3.32/1.00  
% 3.32/1.00  fof(f61,plain,(
% 3.32/1.00    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.32/1.00    inference(cnf_transformation,[],[f40])).
% 3.32/1.00  
% 3.32/1.00  fof(f62,plain,(
% 3.32/1.00    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.32/1.00    inference(cnf_transformation,[],[f40])).
% 3.32/1.00  
% 3.32/1.00  fof(f3,axiom,(
% 3.32/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f32,plain,(
% 3.32/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.32/1.00    inference(nnf_transformation,[],[f3])).
% 3.32/1.00  
% 3.32/1.00  fof(f44,plain,(
% 3.32/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f32])).
% 3.32/1.00  
% 3.32/1.00  fof(f2,axiom,(
% 3.32/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f16,plain,(
% 3.32/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.32/1.00    inference(ennf_transformation,[],[f2])).
% 3.32/1.00  
% 3.32/1.00  fof(f42,plain,(
% 3.32/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f16])).
% 3.32/1.00  
% 3.32/1.00  fof(f1,axiom,(
% 3.32/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f15,plain,(
% 3.32/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.32/1.00    inference(ennf_transformation,[],[f1])).
% 3.32/1.00  
% 3.32/1.00  fof(f41,plain,(
% 3.32/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f15])).
% 3.32/1.00  
% 3.32/1.00  fof(f43,plain,(
% 3.32/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f32])).
% 3.32/1.00  
% 3.32/1.00  cnf(c_20,negated_conjecture,
% 3.32/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.32/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1254,plain,
% 3.32/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7,plain,
% 3.32/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | ~ l1_pre_topc(X1)
% 3.32/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_21,negated_conjecture,
% 3.32/1.00      ( l1_pre_topc(sK0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_445,plain,
% 3.32/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | k2_pre_topc(X1,X0) = X0
% 3.32/1.00      | sK0 != X1 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_446,plain,
% 3.32/1.00      ( ~ v4_pre_topc(X0,sK0)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | k2_pre_topc(sK0,X0) = X0 ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_445]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_12,plain,
% 3.32/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.32/1.00      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | ~ l1_pre_topc(X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_391,plain,
% 3.32/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.32/1.00      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | sK0 != X1 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_392,plain,
% 3.32/1.00      ( ~ v3_pre_topc(X0,sK0)
% 3.32/1.00      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_391]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_508,plain,
% 3.32/1.00      ( ~ v3_pre_topc(X0,sK0)
% 3.32/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | k2_pre_topc(sK0,X1) = X1
% 3.32/1.00      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 3.32/1.00      | sK0 != sK0 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_446,c_392]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_509,plain,
% 3.32/1.00      ( ~ v3_pre_topc(X0,sK0)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_508]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_521,plain,
% 3.32/1.00      ( ~ v3_pre_topc(X0,sK0)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
% 3.32/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_509,c_4]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_18,negated_conjecture,
% 3.32/1.00      ( v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_557,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.32/1.00      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 3.32/1.00      | sK3 != X0
% 3.32/1.00      | sK0 != sK0 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_521,c_18]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_558,plain,
% 3.32/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.32/1.00      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_557]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_19,negated_conjecture,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_560,plain,
% 3.32/1.00      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.32/1.00      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_558,c_19]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1248,plain,
% 3.32/1.00      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
% 3.32/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_13,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.32/1.00      | ~ l1_pre_topc(X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_379,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.32/1.00      | sK0 != X1 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_380,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_379]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1390,plain,
% 3.32/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_380]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_15,negated_conjecture,
% 3.32/1.00      ( ~ v3_pre_topc(X0,sK0)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ r2_hidden(sK1,X0)
% 3.32/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.32/1.00      | ~ r1_tarski(X0,sK2) ),
% 3.32/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_10,plain,
% 3.32/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.32/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.32/1.00      | ~ l1_pre_topc(X0)
% 3.32/1.00      | ~ v2_pre_topc(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_22,negated_conjecture,
% 3.32/1.00      ( v2_pre_topc(sK0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_315,plain,
% 3.32/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.32/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.32/1.00      | ~ l1_pre_topc(X0)
% 3.32/1.00      | sK0 != X0 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_316,plain,
% 3.32/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ l1_pre_topc(sK0) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_315]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_320,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_316,c_21]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_321,plain,
% 3.32/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.32/1.00      inference(renaming,[status(thm)],[c_320]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_591,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ r2_hidden(sK1,X0)
% 3.32/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.32/1.00      | ~ r1_tarski(X0,sK2)
% 3.32/1.00      | k1_tops_1(sK0,X1) != X0
% 3.32/1.00      | sK0 != sK0 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_321]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_592,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.32/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.32/1.00      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_591]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_9,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | ~ l1_pre_topc(X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_421,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | sK0 != X1 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_422,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_596,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.32/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.32/1.00      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_592,c_422]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1396,plain,
% 3.32/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.32/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_596]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2281,plain,
% 3.32/1.00      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_1248,c_20,c_560,c_1390,c_1396]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1255,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.32/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_25,plain,
% 3.32/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_26,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.32/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1391,plain,
% 3.32/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.32/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1390]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1397,plain,
% 3.32/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.32/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 3.32/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1396]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1434,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_1255,c_25,c_26,c_1391,c_1397]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | ~ l1_pre_topc(X1)
% 3.32/1.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_433,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 3.32/1.00      | sK0 != X1 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_434,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_433]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1250,plain,
% 3.32/1.00      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.32/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2063,plain,
% 3.32/1.00      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1434,c_1250]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2284,plain,
% 3.32/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_2281,c_2063]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1258,plain,
% 3.32/1.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.32/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2392,plain,
% 3.32/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1434,c_1258]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3016,plain,
% 3.32/1.00      ( k1_tops_1(sK0,sK3) = sK3 ),
% 3.32/1.00      inference(light_normalisation,[status(thm)],[c_2284,c_2392]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_14,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | ~ r1_tarski(X0,X2)
% 3.32/1.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.32/1.00      | ~ l1_pre_topc(X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_361,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.00      | ~ r1_tarski(X0,X2)
% 3.32/1.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.32/1.00      | sK0 != X1 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_362,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.32/1.00      | ~ r1_tarski(X0,X1)
% 3.32/1.00      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_361]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1253,plain,
% 3.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.32/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.32/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.32/1.00      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3027,plain,
% 3.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.32/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.32/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.32/1.00      | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_3016,c_1253]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8591,plain,
% 3.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.32/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.32/1.00      | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_3027,c_25,c_26,c_1391,c_1397]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8602,plain,
% 3.32/1.00      ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top
% 3.32/1.00      | r1_tarski(sK3,sK2) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1254,c_8591]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_17,negated_conjecture,
% 3.32/1.00      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(sK3,sK2) ),
% 3.32/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_28,plain,
% 3.32/1.00      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.32/1.00      | r1_tarski(sK3,sK2) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8651,plain,
% 3.32/1.00      ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_8602,c_25,c_28,c_1391,c_1397]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_16,negated_conjecture,
% 3.32/1.00      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r2_hidden(sK1,sK3) ),
% 3.32/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1257,plain,
% 3.32/1.00      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.32/1.00      | r2_hidden(sK1,sK3) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_29,plain,
% 3.32/1.00      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.32/1.00      | r2_hidden(sK1,sK3) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1428,plain,
% 3.32/1.00      ( r2_hidden(sK1,sK3) = iProver_top ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_1257,c_25,c_29,c_1391,c_1397]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2,plain,
% 3.32/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1261,plain,
% 3.32/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.32/1.00      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1,plain,
% 3.32/1.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.32/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1262,plain,
% 3.32/1.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1771,plain,
% 3.32/1.00      ( k2_xboole_0(k1_tarski(X0),X1) = X1
% 3.32/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1261,c_1262]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3268,plain,
% 3.32/1.00      ( k2_xboole_0(k1_tarski(sK1),sK3) = sK3 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1428,c_1771]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_0,plain,
% 3.32/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1263,plain,
% 3.32/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.32/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4193,plain,
% 3.32/1.00      ( r1_tarski(k1_tarski(sK1),X0) = iProver_top
% 3.32/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_3268,c_1263]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3,plain,
% 3.32/1.00      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1260,plain,
% 3.32/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.32/1.00      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4201,plain,
% 3.32/1.00      ( r2_hidden(sK1,X0) = iProver_top
% 3.32/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_4193,c_1260]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8658,plain,
% 3.32/1.00      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_8651,c_4201]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(contradiction,plain,
% 3.32/1.00      ( $false ),
% 3.32/1.00      inference(minisat,[status(thm)],[c_8658,c_1397,c_1391,c_25]) ).
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/1.00  
% 3.32/1.00  ------                               Statistics
% 3.32/1.00  
% 3.32/1.00  ------ General
% 3.32/1.00  
% 3.32/1.00  abstr_ref_over_cycles:                  0
% 3.32/1.00  abstr_ref_under_cycles:                 0
% 3.32/1.00  gc_basic_clause_elim:                   0
% 3.32/1.00  forced_gc_time:                         0
% 3.32/1.00  parsing_time:                           0.009
% 3.32/1.00  unif_index_cands_time:                  0.
% 3.32/1.00  unif_index_add_time:                    0.
% 3.32/1.00  orderings_time:                         0.
% 3.32/1.00  out_proof_time:                         0.01
% 3.32/1.00  total_time:                             0.276
% 3.32/1.00  num_of_symbols:                         49
% 3.32/1.00  num_of_terms:                           8608
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing
% 3.32/1.00  
% 3.32/1.00  num_of_splits:                          0
% 3.32/1.00  num_of_split_atoms:                     0
% 3.32/1.00  num_of_reused_defs:                     0
% 3.32/1.00  num_eq_ax_congr_red:                    11
% 3.32/1.00  num_of_sem_filtered_clauses:            1
% 3.32/1.00  num_of_subtypes:                        0
% 3.32/1.00  monotx_restored_types:                  0
% 3.32/1.00  sat_num_of_epr_types:                   0
% 3.32/1.00  sat_num_of_non_cyclic_types:            0
% 3.32/1.00  sat_guarded_non_collapsed_types:        0
% 3.32/1.00  num_pure_diseq_elim:                    0
% 3.32/1.00  simp_replaced_by:                       0
% 3.32/1.00  res_preprocessed:                       98
% 3.32/1.00  prep_upred:                             0
% 3.32/1.00  prep_unflattend:                        15
% 3.32/1.00  smt_new_axioms:                         0
% 3.32/1.00  pred_elim_cands:                        3
% 3.32/1.00  pred_elim:                              4
% 3.32/1.00  pred_elim_cl:                           5
% 3.32/1.00  pred_elim_cycles:                       6
% 3.32/1.00  merged_defs:                            8
% 3.32/1.00  merged_defs_ncl:                        0
% 3.32/1.00  bin_hyper_res:                          8
% 3.32/1.00  prep_cycles:                            4
% 3.32/1.00  pred_elim_time:                         0.007
% 3.32/1.00  splitting_time:                         0.
% 3.32/1.00  sem_filter_time:                        0.
% 3.32/1.00  monotx_time:                            0.
% 3.32/1.00  subtype_inf_time:                       0.
% 3.32/1.00  
% 3.32/1.00  ------ Problem properties
% 3.32/1.00  
% 3.32/1.00  clauses:                                18
% 3.32/1.00  conjectures:                            4
% 3.32/1.00  epr:                                    0
% 3.32/1.00  horn:                                   14
% 3.32/1.00  ground:                                 5
% 3.32/1.00  unary:                                  1
% 3.32/1.00  binary:                                 14
% 3.32/1.00  lits:                                   42
% 3.32/1.00  lits_eq:                                6
% 3.32/1.00  fd_pure:                                0
% 3.32/1.00  fd_pseudo:                              0
% 3.32/1.00  fd_cond:                                0
% 3.32/1.00  fd_pseudo_cond:                         0
% 3.32/1.00  ac_symbols:                             0
% 3.32/1.00  
% 3.32/1.00  ------ Propositional Solver
% 3.32/1.00  
% 3.32/1.00  prop_solver_calls:                      29
% 3.32/1.00  prop_fast_solver_calls:                 770
% 3.32/1.00  smt_solver_calls:                       0
% 3.32/1.00  smt_fast_solver_calls:                  0
% 3.32/1.00  prop_num_of_clauses:                    3503
% 3.32/1.00  prop_preprocess_simplified:             8415
% 3.32/1.00  prop_fo_subsumed:                       26
% 3.32/1.00  prop_solver_time:                       0.
% 3.32/1.00  smt_solver_time:                        0.
% 3.32/1.00  smt_fast_solver_time:                   0.
% 3.32/1.00  prop_fast_solver_time:                  0.
% 3.32/1.00  prop_unsat_core_time:                   0.
% 3.32/1.00  
% 3.32/1.00  ------ QBF
% 3.32/1.00  
% 3.32/1.00  qbf_q_res:                              0
% 3.32/1.00  qbf_num_tautologies:                    0
% 3.32/1.00  qbf_prep_cycles:                        0
% 3.32/1.00  
% 3.32/1.00  ------ BMC1
% 3.32/1.00  
% 3.32/1.00  bmc1_current_bound:                     -1
% 3.32/1.00  bmc1_last_solved_bound:                 -1
% 3.32/1.00  bmc1_unsat_core_size:                   -1
% 3.32/1.00  bmc1_unsat_core_parents_size:           -1
% 3.32/1.00  bmc1_merge_next_fun:                    0
% 3.32/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.32/1.00  
% 3.32/1.00  ------ Instantiation
% 3.32/1.00  
% 3.32/1.00  inst_num_of_clauses:                    1289
% 3.32/1.00  inst_num_in_passive:                    712
% 3.32/1.00  inst_num_in_active:                     466
% 3.32/1.00  inst_num_in_unprocessed:                111
% 3.32/1.00  inst_num_of_loops:                      500
% 3.32/1.00  inst_num_of_learning_restarts:          0
% 3.32/1.00  inst_num_moves_active_passive:          33
% 3.32/1.00  inst_lit_activity:                      0
% 3.32/1.00  inst_lit_activity_moves:                1
% 3.32/1.00  inst_num_tautologies:                   0
% 3.32/1.00  inst_num_prop_implied:                  0
% 3.32/1.00  inst_num_existing_simplified:           0
% 3.32/1.00  inst_num_eq_res_simplified:             0
% 3.32/1.00  inst_num_child_elim:                    0
% 3.32/1.00  inst_num_of_dismatching_blockings:      61
% 3.32/1.00  inst_num_of_non_proper_insts:           941
% 3.32/1.00  inst_num_of_duplicates:                 0
% 3.32/1.00  inst_inst_num_from_inst_to_res:         0
% 3.32/1.00  inst_dismatching_checking_time:         0.
% 3.32/1.00  
% 3.32/1.00  ------ Resolution
% 3.32/1.00  
% 3.32/1.00  res_num_of_clauses:                     0
% 3.32/1.00  res_num_in_passive:                     0
% 3.32/1.00  res_num_in_active:                      0
% 3.32/1.00  res_num_of_loops:                       102
% 3.32/1.00  res_forward_subset_subsumed:            9
% 3.32/1.00  res_backward_subset_subsumed:           0
% 3.32/1.00  res_forward_subsumed:                   0
% 3.32/1.00  res_backward_subsumed:                  0
% 3.32/1.00  res_forward_subsumption_resolution:     2
% 3.32/1.00  res_backward_subsumption_resolution:    0
% 3.32/1.00  res_clause_to_clause_subsumption:       591
% 3.32/1.00  res_orphan_elimination:                 0
% 3.32/1.00  res_tautology_del:                      36
% 3.32/1.00  res_num_eq_res_simplified:              0
% 3.32/1.00  res_num_sel_changes:                    0
% 3.32/1.00  res_moves_from_active_to_pass:          0
% 3.32/1.00  
% 3.32/1.00  ------ Superposition
% 3.32/1.00  
% 3.32/1.00  sup_time_total:                         0.
% 3.32/1.00  sup_time_generating:                    0.
% 3.32/1.00  sup_time_sim_full:                      0.
% 3.32/1.00  sup_time_sim_immed:                     0.
% 3.32/1.00  
% 3.32/1.00  sup_num_of_clauses:                     208
% 3.32/1.00  sup_num_in_active:                      94
% 3.32/1.00  sup_num_in_passive:                     114
% 3.32/1.00  sup_num_of_loops:                       99
% 3.32/1.00  sup_fw_superposition:                   171
% 3.32/1.00  sup_bw_superposition:                   142
% 3.32/1.00  sup_immediate_simplified:               112
% 3.32/1.00  sup_given_eliminated:                   0
% 3.32/1.00  comparisons_done:                       0
% 3.32/1.00  comparisons_avoided:                    0
% 3.32/1.00  
% 3.32/1.00  ------ Simplifications
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  sim_fw_subset_subsumed:                 15
% 3.32/1.00  sim_bw_subset_subsumed:                 1
% 3.32/1.00  sim_fw_subsumed:                        12
% 3.32/1.00  sim_bw_subsumed:                        0
% 3.32/1.00  sim_fw_subsumption_res:                 0
% 3.32/1.00  sim_bw_subsumption_res:                 0
% 3.32/1.00  sim_tautology_del:                      17
% 3.32/1.00  sim_eq_tautology_del:                   40
% 3.32/1.00  sim_eq_res_simp:                        0
% 3.32/1.00  sim_fw_demodulated:                     0
% 3.32/1.00  sim_bw_demodulated:                     7
% 3.32/1.00  sim_light_normalised:                   97
% 3.32/1.00  sim_joinable_taut:                      0
% 3.32/1.00  sim_joinable_simp:                      0
% 3.32/1.00  sim_ac_normalised:                      0
% 3.32/1.00  sim_smt_subsumption:                    0
% 3.32/1.00  
%------------------------------------------------------------------------------
