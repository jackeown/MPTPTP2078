%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:00 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  145 (1220 expanded)
%              Number of clauses        :   87 ( 296 expanded)
%              Number of leaves         :   15 ( 301 expanded)
%              Depth                    :   28
%              Number of atoms          :  531 (10619 expanded)
%              Number of equality atoms :  107 ( 203 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
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

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
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

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f57,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1219,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1220,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_25,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_351,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_352,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_1273,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_1274,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_14,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,sK2)
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_9,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_305,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_306,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_20])).

cnf(c_311,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_310])).

cnf(c_588,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_311])).

cnf(c_589,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_394])).

cnf(c_594,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_593])).

cnf(c_1358,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_1359,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1358])).

cnf(c_1422,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1220,c_24,c_25,c_1274,c_1359])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_432,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_433,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_1213,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1224,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1225,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1740,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1224,c_1225])).

cnf(c_2971,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,k1_tops_1(sK0,X0)) != iProver_top
    | r2_hidden(X2,k1_tops_1(sK0,X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1740])).

cnf(c_8187,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK0,X0)) = iProver_top
    | r2_hidden(X1,k1_tops_1(sK0,sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_2971])).

cnf(c_6,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_417,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_418,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_363,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_364,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_496,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) = X1
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_418,c_364])).

cnf(c_497,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_548,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | sK3 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_497,c_17])).

cnf(c_549,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_551,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_18])).

cnf(c_552,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(renaming,[status(thm)],[c_551])).

cnf(c_1211,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1371,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1628,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_170,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_216,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_170])).

cnf(c_1382,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_1786,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_2503,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1211,c_19,c_18,c_552,c_1273,c_1358,c_1628,c_1786])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_1214,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_2040,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_1422,c_1214])).

cnf(c_2505,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_2503,c_2040])).

cnf(c_1223,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1679,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1223])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_217,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_170])).

cnf(c_1217,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_2320,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1679,c_1217])).

cnf(c_2506,plain,
    ( k1_tops_1(sK0,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2505,c_2320])).

cnf(c_8191,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK0,X0)) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8187,c_2506])).

cnf(c_8500,plain,
    ( r1_tarski(sK3,sK2) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_8191])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( r1_tarski(sK3,sK2) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8581,plain,
    ( r2_hidden(X0,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8500,c_24,c_27,c_1274,c_1359])).

cnf(c_1209,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),sK2) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,X0)) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_1672,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1209,c_24,c_1274,c_1359])).

cnf(c_8587,plain,
    ( r2_hidden(sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8581,c_1672])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8587,c_1359,c_1274,c_28,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:06:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.68/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.98  
% 3.68/0.98  ------  iProver source info
% 3.68/0.98  
% 3.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.98  git: non_committed_changes: false
% 3.68/0.98  git: last_make_outside_of_git: false
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options
% 3.68/0.98  
% 3.68/0.98  --out_options                           all
% 3.68/0.98  --tptp_safe_out                         true
% 3.68/0.98  --problem_path                          ""
% 3.68/0.98  --include_path                          ""
% 3.68/0.98  --clausifier                            res/vclausify_rel
% 3.68/0.98  --clausifier_options                    ""
% 3.68/0.98  --stdin                                 false
% 3.68/0.98  --stats_out                             all
% 3.68/0.98  
% 3.68/0.98  ------ General Options
% 3.68/0.98  
% 3.68/0.98  --fof                                   false
% 3.68/0.98  --time_out_real                         305.
% 3.68/0.98  --time_out_virtual                      -1.
% 3.68/0.98  --symbol_type_check                     false
% 3.68/0.98  --clausify_out                          false
% 3.68/0.98  --sig_cnt_out                           false
% 3.68/0.98  --trig_cnt_out                          false
% 3.68/0.98  --trig_cnt_out_tolerance                1.
% 3.68/0.98  --trig_cnt_out_sk_spl                   false
% 3.68/0.98  --abstr_cl_out                          false
% 3.68/0.98  
% 3.68/0.98  ------ Global Options
% 3.68/0.98  
% 3.68/0.98  --schedule                              default
% 3.68/0.98  --add_important_lit                     false
% 3.68/0.98  --prop_solver_per_cl                    1000
% 3.68/0.98  --min_unsat_core                        false
% 3.68/0.98  --soft_assumptions                      false
% 3.68/0.98  --soft_lemma_size                       3
% 3.68/0.98  --prop_impl_unit_size                   0
% 3.68/0.98  --prop_impl_unit                        []
% 3.68/0.98  --share_sel_clauses                     true
% 3.68/0.98  --reset_solvers                         false
% 3.68/0.98  --bc_imp_inh                            [conj_cone]
% 3.68/0.98  --conj_cone_tolerance                   3.
% 3.68/0.98  --extra_neg_conj                        none
% 3.68/0.98  --large_theory_mode                     true
% 3.68/0.98  --prolific_symb_bound                   200
% 3.68/0.98  --lt_threshold                          2000
% 3.68/0.98  --clause_weak_htbl                      true
% 3.68/0.98  --gc_record_bc_elim                     false
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing Options
% 3.68/0.98  
% 3.68/0.98  --preprocessing_flag                    true
% 3.68/0.98  --time_out_prep_mult                    0.1
% 3.68/0.98  --splitting_mode                        input
% 3.68/0.98  --splitting_grd                         true
% 3.68/0.98  --splitting_cvd                         false
% 3.68/0.98  --splitting_cvd_svl                     false
% 3.68/0.98  --splitting_nvd                         32
% 3.68/0.98  --sub_typing                            true
% 3.68/0.98  --prep_gs_sim                           true
% 3.68/0.98  --prep_unflatten                        true
% 3.68/0.98  --prep_res_sim                          true
% 3.68/0.98  --prep_upred                            true
% 3.68/0.98  --prep_sem_filter                       exhaustive
% 3.68/0.98  --prep_sem_filter_out                   false
% 3.68/0.98  --pred_elim                             true
% 3.68/0.98  --res_sim_input                         true
% 3.68/0.98  --eq_ax_congr_red                       true
% 3.68/0.98  --pure_diseq_elim                       true
% 3.68/0.98  --brand_transform                       false
% 3.68/0.98  --non_eq_to_eq                          false
% 3.68/0.98  --prep_def_merge                        true
% 3.68/0.98  --prep_def_merge_prop_impl              false
% 3.68/0.98  --prep_def_merge_mbd                    true
% 3.68/0.98  --prep_def_merge_tr_red                 false
% 3.68/0.98  --prep_def_merge_tr_cl                  false
% 3.68/0.98  --smt_preprocessing                     true
% 3.68/0.98  --smt_ac_axioms                         fast
% 3.68/0.98  --preprocessed_out                      false
% 3.68/0.98  --preprocessed_stats                    false
% 3.68/0.98  
% 3.68/0.98  ------ Abstraction refinement Options
% 3.68/0.98  
% 3.68/0.98  --abstr_ref                             []
% 3.68/0.98  --abstr_ref_prep                        false
% 3.68/0.98  --abstr_ref_until_sat                   false
% 3.68/0.98  --abstr_ref_sig_restrict                funpre
% 3.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.98  --abstr_ref_under                       []
% 3.68/0.98  
% 3.68/0.98  ------ SAT Options
% 3.68/0.98  
% 3.68/0.98  --sat_mode                              false
% 3.68/0.98  --sat_fm_restart_options                ""
% 3.68/0.98  --sat_gr_def                            false
% 3.68/0.98  --sat_epr_types                         true
% 3.68/0.98  --sat_non_cyclic_types                  false
% 3.68/0.98  --sat_finite_models                     false
% 3.68/0.98  --sat_fm_lemmas                         false
% 3.68/0.98  --sat_fm_prep                           false
% 3.68/0.98  --sat_fm_uc_incr                        true
% 3.68/0.98  --sat_out_model                         small
% 3.68/0.98  --sat_out_clauses                       false
% 3.68/0.98  
% 3.68/0.98  ------ QBF Options
% 3.68/0.98  
% 3.68/0.98  --qbf_mode                              false
% 3.68/0.98  --qbf_elim_univ                         false
% 3.68/0.98  --qbf_dom_inst                          none
% 3.68/0.98  --qbf_dom_pre_inst                      false
% 3.68/0.98  --qbf_sk_in                             false
% 3.68/0.98  --qbf_pred_elim                         true
% 3.68/0.98  --qbf_split                             512
% 3.68/0.98  
% 3.68/0.98  ------ BMC1 Options
% 3.68/0.98  
% 3.68/0.98  --bmc1_incremental                      false
% 3.68/0.98  --bmc1_axioms                           reachable_all
% 3.68/0.98  --bmc1_min_bound                        0
% 3.68/0.98  --bmc1_max_bound                        -1
% 3.68/0.98  --bmc1_max_bound_default                -1
% 3.68/0.98  --bmc1_symbol_reachability              true
% 3.68/0.98  --bmc1_property_lemmas                  false
% 3.68/0.98  --bmc1_k_induction                      false
% 3.68/0.98  --bmc1_non_equiv_states                 false
% 3.68/0.98  --bmc1_deadlock                         false
% 3.68/0.98  --bmc1_ucm                              false
% 3.68/0.98  --bmc1_add_unsat_core                   none
% 3.68/0.98  --bmc1_unsat_core_children              false
% 3.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.98  --bmc1_out_stat                         full
% 3.68/0.98  --bmc1_ground_init                      false
% 3.68/0.98  --bmc1_pre_inst_next_state              false
% 3.68/0.98  --bmc1_pre_inst_state                   false
% 3.68/0.98  --bmc1_pre_inst_reach_state             false
% 3.68/0.98  --bmc1_out_unsat_core                   false
% 3.68/0.98  --bmc1_aig_witness_out                  false
% 3.68/0.98  --bmc1_verbose                          false
% 3.68/0.98  --bmc1_dump_clauses_tptp                false
% 3.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.98  --bmc1_dump_file                        -
% 3.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.98  --bmc1_ucm_extend_mode                  1
% 3.68/0.98  --bmc1_ucm_init_mode                    2
% 3.68/0.98  --bmc1_ucm_cone_mode                    none
% 3.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.98  --bmc1_ucm_relax_model                  4
% 3.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.98  --bmc1_ucm_layered_model                none
% 3.68/0.98  --bmc1_ucm_max_lemma_size               10
% 3.68/0.98  
% 3.68/0.98  ------ AIG Options
% 3.68/0.98  
% 3.68/0.98  --aig_mode                              false
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation Options
% 3.68/0.98  
% 3.68/0.98  --instantiation_flag                    true
% 3.68/0.98  --inst_sos_flag                         true
% 3.68/0.98  --inst_sos_phase                        true
% 3.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel_side                     num_symb
% 3.68/0.98  --inst_solver_per_active                1400
% 3.68/0.98  --inst_solver_calls_frac                1.
% 3.68/0.98  --inst_passive_queue_type               priority_queues
% 3.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.98  --inst_passive_queues_freq              [25;2]
% 3.68/0.98  --inst_dismatching                      true
% 3.68/0.98  --inst_eager_unprocessed_to_passive     true
% 3.68/0.98  --inst_prop_sim_given                   true
% 3.68/0.98  --inst_prop_sim_new                     false
% 3.68/0.98  --inst_subs_new                         false
% 3.68/0.98  --inst_eq_res_simp                      false
% 3.68/0.98  --inst_subs_given                       false
% 3.68/0.98  --inst_orphan_elimination               true
% 3.68/0.98  --inst_learning_loop_flag               true
% 3.68/0.98  --inst_learning_start                   3000
% 3.68/0.98  --inst_learning_factor                  2
% 3.68/0.98  --inst_start_prop_sim_after_learn       3
% 3.68/0.98  --inst_sel_renew                        solver
% 3.68/0.98  --inst_lit_activity_flag                true
% 3.68/0.98  --inst_restr_to_given                   false
% 3.68/0.98  --inst_activity_threshold               500
% 3.68/0.98  --inst_out_proof                        true
% 3.68/0.98  
% 3.68/0.98  ------ Resolution Options
% 3.68/0.98  
% 3.68/0.98  --resolution_flag                       true
% 3.68/0.98  --res_lit_sel                           adaptive
% 3.68/0.98  --res_lit_sel_side                      none
% 3.68/0.98  --res_ordering                          kbo
% 3.68/0.98  --res_to_prop_solver                    active
% 3.68/0.98  --res_prop_simpl_new                    false
% 3.68/0.98  --res_prop_simpl_given                  true
% 3.68/0.98  --res_passive_queue_type                priority_queues
% 3.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.98  --res_passive_queues_freq               [15;5]
% 3.68/0.98  --res_forward_subs                      full
% 3.68/0.98  --res_backward_subs                     full
% 3.68/0.98  --res_forward_subs_resolution           true
% 3.68/0.98  --res_backward_subs_resolution          true
% 3.68/0.98  --res_orphan_elimination                true
% 3.68/0.98  --res_time_limit                        2.
% 3.68/0.98  --res_out_proof                         true
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Options
% 3.68/0.98  
% 3.68/0.98  --superposition_flag                    true
% 3.68/0.98  --sup_passive_queue_type                priority_queues
% 3.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.98  --demod_completeness_check              fast
% 3.68/0.98  --demod_use_ground                      true
% 3.68/0.98  --sup_to_prop_solver                    passive
% 3.68/0.98  --sup_prop_simpl_new                    true
% 3.68/0.98  --sup_prop_simpl_given                  true
% 3.68/0.98  --sup_fun_splitting                     true
% 3.68/0.98  --sup_smt_interval                      50000
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Simplification Setup
% 3.68/0.98  
% 3.68/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_immed_triv                        [TrivRules]
% 3.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_bw_main                     []
% 3.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_input_bw                          []
% 3.68/0.98  
% 3.68/0.98  ------ Combination Options
% 3.68/0.98  
% 3.68/0.98  --comb_res_mult                         3
% 3.68/0.98  --comb_sup_mult                         2
% 3.68/0.98  --comb_inst_mult                        10
% 3.68/0.98  
% 3.68/0.98  ------ Debug Options
% 3.68/0.98  
% 3.68/0.98  --dbg_backtrace                         false
% 3.68/0.98  --dbg_dump_prop_clauses                 false
% 3.68/0.98  --dbg_dump_prop_clauses_file            -
% 3.68/0.98  --dbg_out_stat                          false
% 3.68/0.98  ------ Parsing...
% 3.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  ------ Proving...
% 3.68/0.98  ------ Problem Properties 
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  clauses                                 17
% 3.68/0.98  conjectures                             4
% 3.68/0.98  EPR                                     0
% 3.68/0.98  Horn                                    13
% 3.68/0.98  unary                                   1
% 3.68/0.98  binary                                  10
% 3.68/0.98  lits                                    44
% 3.68/0.98  lits eq                                 5
% 3.68/0.98  fd_pure                                 0
% 3.68/0.98  fd_pseudo                               0
% 3.68/0.98  fd_cond                                 0
% 3.68/0.98  fd_pseudo_cond                          0
% 3.68/0.98  AC symbols                              0
% 3.68/0.98  
% 3.68/0.98  ------ Schedule dynamic 5 is on 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  Current options:
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options
% 3.68/0.98  
% 3.68/0.98  --out_options                           all
% 3.68/0.98  --tptp_safe_out                         true
% 3.68/0.98  --problem_path                          ""
% 3.68/0.98  --include_path                          ""
% 3.68/0.98  --clausifier                            res/vclausify_rel
% 3.68/0.98  --clausifier_options                    ""
% 3.68/0.98  --stdin                                 false
% 3.68/0.98  --stats_out                             all
% 3.68/0.98  
% 3.68/0.98  ------ General Options
% 3.68/0.98  
% 3.68/0.98  --fof                                   false
% 3.68/0.98  --time_out_real                         305.
% 3.68/0.98  --time_out_virtual                      -1.
% 3.68/0.98  --symbol_type_check                     false
% 3.68/0.98  --clausify_out                          false
% 3.68/0.98  --sig_cnt_out                           false
% 3.68/0.98  --trig_cnt_out                          false
% 3.68/0.98  --trig_cnt_out_tolerance                1.
% 3.68/0.98  --trig_cnt_out_sk_spl                   false
% 3.68/0.98  --abstr_cl_out                          false
% 3.68/0.98  
% 3.68/0.98  ------ Global Options
% 3.68/0.98  
% 3.68/0.98  --schedule                              default
% 3.68/0.98  --add_important_lit                     false
% 3.68/0.98  --prop_solver_per_cl                    1000
% 3.68/0.98  --min_unsat_core                        false
% 3.68/0.98  --soft_assumptions                      false
% 3.68/0.98  --soft_lemma_size                       3
% 3.68/0.98  --prop_impl_unit_size                   0
% 3.68/0.98  --prop_impl_unit                        []
% 3.68/0.98  --share_sel_clauses                     true
% 3.68/0.98  --reset_solvers                         false
% 3.68/0.98  --bc_imp_inh                            [conj_cone]
% 3.68/0.98  --conj_cone_tolerance                   3.
% 3.68/0.98  --extra_neg_conj                        none
% 3.68/0.98  --large_theory_mode                     true
% 3.68/0.98  --prolific_symb_bound                   200
% 3.68/0.98  --lt_threshold                          2000
% 3.68/0.98  --clause_weak_htbl                      true
% 3.68/0.98  --gc_record_bc_elim                     false
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing Options
% 3.68/0.98  
% 3.68/0.98  --preprocessing_flag                    true
% 3.68/0.98  --time_out_prep_mult                    0.1
% 3.68/0.98  --splitting_mode                        input
% 3.68/0.98  --splitting_grd                         true
% 3.68/0.98  --splitting_cvd                         false
% 3.68/0.98  --splitting_cvd_svl                     false
% 3.68/0.98  --splitting_nvd                         32
% 3.68/0.98  --sub_typing                            true
% 3.68/0.98  --prep_gs_sim                           true
% 3.68/0.98  --prep_unflatten                        true
% 3.68/0.98  --prep_res_sim                          true
% 3.68/0.98  --prep_upred                            true
% 3.68/0.98  --prep_sem_filter                       exhaustive
% 3.68/0.98  --prep_sem_filter_out                   false
% 3.68/0.98  --pred_elim                             true
% 3.68/0.98  --res_sim_input                         true
% 3.68/0.98  --eq_ax_congr_red                       true
% 3.68/0.98  --pure_diseq_elim                       true
% 3.68/0.98  --brand_transform                       false
% 3.68/0.98  --non_eq_to_eq                          false
% 3.68/0.98  --prep_def_merge                        true
% 3.68/0.98  --prep_def_merge_prop_impl              false
% 3.68/0.98  --prep_def_merge_mbd                    true
% 3.68/0.98  --prep_def_merge_tr_red                 false
% 3.68/0.98  --prep_def_merge_tr_cl                  false
% 3.68/0.98  --smt_preprocessing                     true
% 3.68/0.98  --smt_ac_axioms                         fast
% 3.68/0.98  --preprocessed_out                      false
% 3.68/0.98  --preprocessed_stats                    false
% 3.68/0.98  
% 3.68/0.98  ------ Abstraction refinement Options
% 3.68/0.98  
% 3.68/0.98  --abstr_ref                             []
% 3.68/0.98  --abstr_ref_prep                        false
% 3.68/0.98  --abstr_ref_until_sat                   false
% 3.68/0.98  --abstr_ref_sig_restrict                funpre
% 3.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.98  --abstr_ref_under                       []
% 3.68/0.98  
% 3.68/0.98  ------ SAT Options
% 3.68/0.98  
% 3.68/0.98  --sat_mode                              false
% 3.68/0.98  --sat_fm_restart_options                ""
% 3.68/0.98  --sat_gr_def                            false
% 3.68/0.98  --sat_epr_types                         true
% 3.68/0.98  --sat_non_cyclic_types                  false
% 3.68/0.98  --sat_finite_models                     false
% 3.68/0.98  --sat_fm_lemmas                         false
% 3.68/0.98  --sat_fm_prep                           false
% 3.68/0.98  --sat_fm_uc_incr                        true
% 3.68/0.98  --sat_out_model                         small
% 3.68/0.98  --sat_out_clauses                       false
% 3.68/0.98  
% 3.68/0.98  ------ QBF Options
% 3.68/0.98  
% 3.68/0.98  --qbf_mode                              false
% 3.68/0.98  --qbf_elim_univ                         false
% 3.68/0.98  --qbf_dom_inst                          none
% 3.68/0.98  --qbf_dom_pre_inst                      false
% 3.68/0.98  --qbf_sk_in                             false
% 3.68/0.98  --qbf_pred_elim                         true
% 3.68/0.98  --qbf_split                             512
% 3.68/0.98  
% 3.68/0.98  ------ BMC1 Options
% 3.68/0.98  
% 3.68/0.98  --bmc1_incremental                      false
% 3.68/0.98  --bmc1_axioms                           reachable_all
% 3.68/0.98  --bmc1_min_bound                        0
% 3.68/0.98  --bmc1_max_bound                        -1
% 3.68/0.98  --bmc1_max_bound_default                -1
% 3.68/0.98  --bmc1_symbol_reachability              true
% 3.68/0.98  --bmc1_property_lemmas                  false
% 3.68/0.98  --bmc1_k_induction                      false
% 3.68/0.98  --bmc1_non_equiv_states                 false
% 3.68/0.98  --bmc1_deadlock                         false
% 3.68/0.98  --bmc1_ucm                              false
% 3.68/0.98  --bmc1_add_unsat_core                   none
% 3.68/0.98  --bmc1_unsat_core_children              false
% 3.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.98  --bmc1_out_stat                         full
% 3.68/0.98  --bmc1_ground_init                      false
% 3.68/0.98  --bmc1_pre_inst_next_state              false
% 3.68/0.98  --bmc1_pre_inst_state                   false
% 3.68/0.98  --bmc1_pre_inst_reach_state             false
% 3.68/0.98  --bmc1_out_unsat_core                   false
% 3.68/0.98  --bmc1_aig_witness_out                  false
% 3.68/0.98  --bmc1_verbose                          false
% 3.68/0.98  --bmc1_dump_clauses_tptp                false
% 3.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.98  --bmc1_dump_file                        -
% 3.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.98  --bmc1_ucm_extend_mode                  1
% 3.68/0.98  --bmc1_ucm_init_mode                    2
% 3.68/0.98  --bmc1_ucm_cone_mode                    none
% 3.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.98  --bmc1_ucm_relax_model                  4
% 3.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.98  --bmc1_ucm_layered_model                none
% 3.68/0.98  --bmc1_ucm_max_lemma_size               10
% 3.68/0.98  
% 3.68/0.98  ------ AIG Options
% 3.68/0.98  
% 3.68/0.98  --aig_mode                              false
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation Options
% 3.68/0.98  
% 3.68/0.98  --instantiation_flag                    true
% 3.68/0.98  --inst_sos_flag                         true
% 3.68/0.98  --inst_sos_phase                        true
% 3.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel_side                     none
% 3.68/0.98  --inst_solver_per_active                1400
% 3.68/0.98  --inst_solver_calls_frac                1.
% 3.68/0.98  --inst_passive_queue_type               priority_queues
% 3.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.98  --inst_passive_queues_freq              [25;2]
% 3.68/0.98  --inst_dismatching                      true
% 3.68/0.98  --inst_eager_unprocessed_to_passive     true
% 3.68/0.98  --inst_prop_sim_given                   true
% 3.68/0.98  --inst_prop_sim_new                     false
% 3.68/0.98  --inst_subs_new                         false
% 3.68/0.98  --inst_eq_res_simp                      false
% 3.68/0.98  --inst_subs_given                       false
% 3.68/0.98  --inst_orphan_elimination               true
% 3.68/0.98  --inst_learning_loop_flag               true
% 3.68/0.98  --inst_learning_start                   3000
% 3.68/0.98  --inst_learning_factor                  2
% 3.68/0.98  --inst_start_prop_sim_after_learn       3
% 3.68/0.98  --inst_sel_renew                        solver
% 3.68/0.98  --inst_lit_activity_flag                true
% 3.68/0.98  --inst_restr_to_given                   false
% 3.68/0.98  --inst_activity_threshold               500
% 3.68/0.98  --inst_out_proof                        true
% 3.68/0.98  
% 3.68/0.98  ------ Resolution Options
% 3.68/0.98  
% 3.68/0.98  --resolution_flag                       false
% 3.68/0.98  --res_lit_sel                           adaptive
% 3.68/0.98  --res_lit_sel_side                      none
% 3.68/0.98  --res_ordering                          kbo
% 3.68/0.98  --res_to_prop_solver                    active
% 3.68/0.98  --res_prop_simpl_new                    false
% 3.68/0.98  --res_prop_simpl_given                  true
% 3.68/0.98  --res_passive_queue_type                priority_queues
% 3.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.98  --res_passive_queues_freq               [15;5]
% 3.68/0.98  --res_forward_subs                      full
% 3.68/0.98  --res_backward_subs                     full
% 3.68/0.98  --res_forward_subs_resolution           true
% 3.68/0.98  --res_backward_subs_resolution          true
% 3.68/0.98  --res_orphan_elimination                true
% 3.68/0.98  --res_time_limit                        2.
% 3.68/0.98  --res_out_proof                         true
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Options
% 3.68/0.98  
% 3.68/0.98  --superposition_flag                    true
% 3.68/0.98  --sup_passive_queue_type                priority_queues
% 3.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.98  --demod_completeness_check              fast
% 3.68/0.98  --demod_use_ground                      true
% 3.68/0.98  --sup_to_prop_solver                    passive
% 3.68/0.98  --sup_prop_simpl_new                    true
% 3.68/0.98  --sup_prop_simpl_given                  true
% 3.68/0.98  --sup_fun_splitting                     true
% 3.68/0.98  --sup_smt_interval                      50000
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Simplification Setup
% 3.68/0.98  
% 3.68/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_immed_triv                        [TrivRules]
% 3.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_bw_main                     []
% 3.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_input_bw                          []
% 3.68/0.98  
% 3.68/0.98  ------ Combination Options
% 3.68/0.98  
% 3.68/0.98  --comb_res_mult                         3
% 3.68/0.98  --comb_sup_mult                         2
% 3.68/0.98  --comb_inst_mult                        10
% 3.68/0.98  
% 3.68/0.98  ------ Debug Options
% 3.68/0.98  
% 3.68/0.98  --dbg_backtrace                         false
% 3.68/0.98  --dbg_dump_prop_clauses                 false
% 3.68/0.98  --dbg_dump_prop_clauses_file            -
% 3.68/0.98  --dbg_out_stat                          false
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS status Theorem for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  fof(f12,conjecture,(
% 3.68/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f13,negated_conjecture,(
% 3.68/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.68/0.98    inference(negated_conjecture,[],[f12])).
% 3.68/0.98  
% 3.68/0.98  fof(f28,plain,(
% 3.68/0.98    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f13])).
% 3.68/0.98  
% 3.68/0.98  fof(f29,plain,(
% 3.68/0.98    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.68/0.98    inference(flattening,[],[f28])).
% 3.68/0.98  
% 3.68/0.98  fof(f32,plain,(
% 3.68/0.98    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.68/0.98    inference(nnf_transformation,[],[f29])).
% 3.68/0.98  
% 3.68/0.98  fof(f33,plain,(
% 3.68/0.98    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.68/0.98    inference(flattening,[],[f32])).
% 3.68/0.98  
% 3.68/0.98  fof(f34,plain,(
% 3.68/0.98    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.68/0.98    inference(rectify,[],[f33])).
% 3.68/0.98  
% 3.68/0.98  fof(f37,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3) & r1_tarski(sK3,X2) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f36,plain,(
% 3.68/0.98    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK1,k1_tops_1(X0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK1,k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f35,plain,(
% 3.68/0.98    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f38,plain,(
% 3.68/0.98    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 3.68/0.98  
% 3.68/0.98  fof(f55,plain,(
% 3.68/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.68/0.98    inference(cnf_transformation,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f56,plain,(
% 3.68/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.68/0.98    inference(cnf_transformation,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f10,axiom,(
% 3.68/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f25,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f10])).
% 3.68/0.98  
% 3.68/0.98  fof(f51,plain,(
% 3.68/0.98    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f25])).
% 3.68/0.98  
% 3.68/0.98  fof(f54,plain,(
% 3.68/0.98    l1_pre_topc(sK0)),
% 3.68/0.98    inference(cnf_transformation,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f60,plain,(
% 3.68/0.98    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f8,axiom,(
% 3.68/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f22,plain,(
% 3.68/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f8])).
% 3.68/0.98  
% 3.68/0.98  fof(f23,plain,(
% 3.68/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/0.98    inference(flattening,[],[f22])).
% 3.68/0.98  
% 3.68/0.98  fof(f48,plain,(
% 3.68/0.98    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f23])).
% 3.68/0.98  
% 3.68/0.98  fof(f53,plain,(
% 3.68/0.98    v2_pre_topc(sK0)),
% 3.68/0.98    inference(cnf_transformation,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f7,axiom,(
% 3.68/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f20,plain,(
% 3.68/0.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f7])).
% 3.68/0.98  
% 3.68/0.98  fof(f21,plain,(
% 3.68/0.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.68/0.98    inference(flattening,[],[f20])).
% 3.68/0.98  
% 3.68/0.98  fof(f47,plain,(
% 3.68/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f21])).
% 3.68/0.98  
% 3.68/0.98  fof(f11,axiom,(
% 3.68/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f26,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f11])).
% 3.68/0.98  
% 3.68/0.98  fof(f27,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.68/0.98    inference(flattening,[],[f26])).
% 3.68/0.98  
% 3.68/0.98  fof(f52,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f27])).
% 3.68/0.98  
% 3.68/0.98  fof(f4,axiom,(
% 3.68/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f30,plain,(
% 3.68/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.68/0.98    inference(nnf_transformation,[],[f4])).
% 3.68/0.98  
% 3.68/0.98  fof(f43,plain,(
% 3.68/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f30])).
% 3.68/0.98  
% 3.68/0.98  fof(f3,axiom,(
% 3.68/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f16,plain,(
% 3.68/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f3])).
% 3.68/0.98  
% 3.68/0.98  fof(f41,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f16])).
% 3.68/0.98  
% 3.68/0.98  fof(f5,axiom,(
% 3.68/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f17,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f5])).
% 3.68/0.98  
% 3.68/0.98  fof(f18,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.68/0.98    inference(flattening,[],[f17])).
% 3.68/0.98  
% 3.68/0.98  fof(f44,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f18])).
% 3.68/0.98  
% 3.68/0.98  fof(f9,axiom,(
% 3.68/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f24,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f9])).
% 3.68/0.98  
% 3.68/0.98  fof(f31,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.68/0.98    inference(nnf_transformation,[],[f24])).
% 3.68/0.98  
% 3.68/0.98  fof(f49,plain,(
% 3.68/0.98    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f31])).
% 3.68/0.98  
% 3.68/0.98  fof(f57,plain,(
% 3.68/0.98    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.68/0.98    inference(cnf_transformation,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f42,plain,(
% 3.68/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f30])).
% 3.68/0.98  
% 3.68/0.98  fof(f1,axiom,(
% 3.68/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f14,plain,(
% 3.68/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f1])).
% 3.68/0.98  
% 3.68/0.98  fof(f39,plain,(
% 3.68/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f14])).
% 3.68/0.98  
% 3.68/0.98  fof(f6,axiom,(
% 3.68/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f19,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f6])).
% 3.68/0.98  
% 3.68/0.98  fof(f46,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f19])).
% 3.68/0.98  
% 3.68/0.98  fof(f2,axiom,(
% 3.68/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f15,plain,(
% 3.68/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f2])).
% 3.68/0.98  
% 3.68/0.98  fof(f40,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f15])).
% 3.68/0.98  
% 3.68/0.98  fof(f58,plain,(
% 3.68/0.98    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.68/0.98    inference(cnf_transformation,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f59,plain,(
% 3.68/0.98    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.68/0.98    inference(cnf_transformation,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  cnf(c_19,negated_conjecture,
% 3.68/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1219,plain,
% 3.68/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_18,negated_conjecture,
% 3.68/0.98      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1220,plain,
% 3.68/0.98      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.68/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_24,plain,
% 3.68/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_25,plain,
% 3.68/0.98      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.68/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12,plain,
% 3.68/0.98      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 3.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.98      | ~ l1_pre_topc(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_20,negated_conjecture,
% 3.68/0.98      ( l1_pre_topc(sK0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_351,plain,
% 3.68/0.98      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 3.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.98      | sK0 != X0 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_352,plain,
% 3.68/0.98      ( r1_tarski(k1_tops_1(sK0,X0),X0)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_351]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1273,plain,
% 3.68/0.98      ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.68/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_352]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1274,plain,
% 3.68/0.98      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
% 3.68/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_14,negated_conjecture,
% 3.68/0.98      ( ~ v3_pre_topc(X0,sK0)
% 3.68/0.98      | ~ r1_tarski(X0,sK2)
% 3.68/0.98      | ~ r2_hidden(sK1,X0)
% 3.68/0.98      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_9,plain,
% 3.68/0.98      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.98      | ~ l1_pre_topc(X0)
% 3.68/0.98      | ~ v2_pre_topc(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_21,negated_conjecture,
% 3.68/0.98      ( v2_pre_topc(sK0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_305,plain,
% 3.68/0.98      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.98      | ~ l1_pre_topc(X0)
% 3.68/0.98      | sK0 != X0 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_306,plain,
% 3.68/0.98      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | ~ l1_pre_topc(sK0) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_305]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_310,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_306,c_20]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_311,plain,
% 3.68/0.98      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_310]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_588,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,sK2)
% 3.68/0.98      | ~ r2_hidden(sK1,X0)
% 3.68/0.98      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | k1_tops_1(sK0,X1) != X0
% 3.68/0.98      | sK0 != sK0 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_311]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_589,plain,
% 3.68/0.98      ( ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
% 3.68/0.98      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.68/0.98      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_588]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.98      | ~ l1_pre_topc(X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_393,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.98      | sK0 != X1 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_394,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_393]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_593,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.68/0.98      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_589,c_394]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_594,plain,
% 3.68/0.98      ( ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
% 3.68/0.98      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.68/0.98      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_593]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1358,plain,
% 3.68/0.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.68/0.98      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_594]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1359,plain,
% 3.68/0.98      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.68/0.98      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 3.68/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1358]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1422,plain,
% 3.68/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_1220,c_24,c_25,c_1274,c_1359]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_13,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1)
% 3.68/0.98      | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.68/0.98      | ~ l1_pre_topc(X2) ),
% 3.68/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_432,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1)
% 3.68/0.98      | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.68/0.98      | sK0 != X2 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_433,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1)
% 3.68/0.98      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_432]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1213,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.68/0.98      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top
% 3.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1224,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,X1)
% 3.68/0.98      | r2_hidden(X0,X2)
% 3.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1225,plain,
% 3.68/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.68/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.68/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1740,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.68/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.68/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1224,c_1225]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2971,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.68/0.98      | r2_hidden(X2,k1_tops_1(sK0,X0)) != iProver_top
% 3.68/0.98      | r2_hidden(X2,k1_tops_1(sK0,X1)) = iProver_top
% 3.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1213,c_1740]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8187,plain,
% 3.68/0.98      ( r1_tarski(sK3,X0) != iProver_top
% 3.68/0.98      | r2_hidden(X1,k1_tops_1(sK0,X0)) = iProver_top
% 3.68/0.98      | r2_hidden(X1,k1_tops_1(sK0,sK3)) != iProver_top
% 3.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1422,c_2971]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6,plain,
% 3.68/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.98      | ~ l1_pre_topc(X1)
% 3.68/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_417,plain,
% 3.68/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.98      | k2_pre_topc(X1,X0) = X0
% 3.68/0.98      | sK0 != X1 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_418,plain,
% 3.68/0.98      ( ~ v4_pre_topc(X0,sK0)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | k2_pre_topc(sK0,X0) = X0 ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_417]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_11,plain,
% 3.68/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.68/0.98      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.98      | ~ l1_pre_topc(X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_363,plain,
% 3.68/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.68/0.98      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.98      | sK0 != X1 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_364,plain,
% 3.68/0.98      ( ~ v3_pre_topc(X0,sK0)
% 3.68/0.98      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_363]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_496,plain,
% 3.68/0.98      ( ~ v3_pre_topc(X0,sK0)
% 3.68/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | k2_pre_topc(sK0,X1) = X1
% 3.68/0.98      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 3.68/0.98      | sK0 != sK0 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_418,c_364]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_497,plain,
% 3.68/0.98      ( ~ v3_pre_topc(X0,sK0)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_496]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_17,negated_conjecture,
% 3.68/0.98      ( v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_548,plain,
% 3.68/0.98      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 3.68/0.98      | sK3 != X0
% 3.68/0.98      | sK0 != sK0 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_497,c_17]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_549,plain,
% 3.68/0.98      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_548]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_551,plain,
% 3.68/0.98      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_549,c_18]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_552,plain,
% 3.68/0.98      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.68/0.98      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_551]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1211,plain,
% 3.68/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
% 3.68/0.98      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.68/0.98      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1371,plain,
% 3.68/0.98      ( r1_tarski(X0,u1_struct_0(sK0))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1628,plain,
% 3.68/0.98      ( r1_tarski(sK3,u1_struct_0(sK0))
% 3.68/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1371]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_0,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_170,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.68/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_216,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1)
% 3.68/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.68/0.98      inference(bin_hyper_res,[status(thm)],[c_0,c_170]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1382,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 3.68/0.98      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_216]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1786,plain,
% 3.68/0.98      ( ~ r1_tarski(sK3,u1_struct_0(sK0))
% 3.68/0.98      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1382]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2503,plain,
% 3.68/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_1211,c_19,c_18,c_552,c_1273,c_1358,c_1628,c_1786]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.98      | ~ l1_pre_topc(X1)
% 3.68/0.98      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_405,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.98      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 3.68/0.98      | sK0 != X1 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_406,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.68/0.98      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_405]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1214,plain,
% 3.68/0.98      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2040,plain,
% 3.68/0.98      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1422,c_1214]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2505,plain,
% 3.68/0.98      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_2503,c_2040]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1223,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1679,plain,
% 3.68/0.98      ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1422,c_1223]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/0.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_217,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.68/0.98      inference(bin_hyper_res,[status(thm)],[c_1,c_170]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1217,plain,
% 3.68/0.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.68/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2320,plain,
% 3.68/0.98      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1679,c_1217]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2506,plain,
% 3.68/0.98      ( k1_tops_1(sK0,sK3) = sK3 ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_2505,c_2320]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8191,plain,
% 3.68/0.98      ( r1_tarski(sK3,X0) != iProver_top
% 3.68/0.98      | r2_hidden(X1,k1_tops_1(sK0,X0)) = iProver_top
% 3.68/0.98      | r2_hidden(X1,sK3) != iProver_top
% 3.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_8187,c_2506]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8500,plain,
% 3.68/0.98      ( r1_tarski(sK3,sK2) != iProver_top
% 3.68/0.98      | r2_hidden(X0,k1_tops_1(sK0,sK2)) = iProver_top
% 3.68/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1219,c_8191]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_16,negated_conjecture,
% 3.68/0.98      ( r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_27,plain,
% 3.68/0.98      ( r1_tarski(sK3,sK2) = iProver_top
% 3.68/0.98      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8581,plain,
% 3.68/0.98      ( r2_hidden(X0,k1_tops_1(sK0,sK2)) = iProver_top
% 3.68/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_8500,c_24,c_27,c_1274,c_1359]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1209,plain,
% 3.68/0.98      ( r1_tarski(k1_tops_1(sK0,X0),sK2) != iProver_top
% 3.68/0.98      | r2_hidden(sK1,k1_tops_1(sK0,X0)) != iProver_top
% 3.68/0.98      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 3.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1672,plain,
% 3.68/0.98      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_1209,c_24,c_1274,c_1359]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8587,plain,
% 3.68/0.98      ( r2_hidden(sK1,sK3) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_8581,c_1672]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_15,negated_conjecture,
% 3.68/0.98      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r2_hidden(sK1,sK3) ),
% 3.68/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_28,plain,
% 3.68/0.98      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.68/0.98      | r2_hidden(sK1,sK3) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(contradiction,plain,
% 3.68/0.98      ( $false ),
% 3.68/0.98      inference(minisat,[status(thm)],[c_8587,c_1359,c_1274,c_28,c_24]) ).
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  ------                               Statistics
% 3.68/0.98  
% 3.68/0.98  ------ General
% 3.68/0.98  
% 3.68/0.98  abstr_ref_over_cycles:                  0
% 3.68/0.98  abstr_ref_under_cycles:                 0
% 3.68/0.98  gc_basic_clause_elim:                   0
% 3.68/0.98  forced_gc_time:                         0
% 3.68/0.98  parsing_time:                           0.009
% 3.68/0.98  unif_index_cands_time:                  0.
% 3.68/0.98  unif_index_add_time:                    0.
% 3.68/0.98  orderings_time:                         0.
% 3.68/0.98  out_proof_time:                         0.011
% 3.68/0.98  total_time:                             0.305
% 3.68/0.98  num_of_symbols:                         47
% 3.68/0.98  num_of_terms:                           10039
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing
% 3.68/0.98  
% 3.68/0.98  num_of_splits:                          0
% 3.68/0.98  num_of_split_atoms:                     0
% 3.68/0.98  num_of_reused_defs:                     0
% 3.68/0.98  num_eq_ax_congr_red:                    2
% 3.68/0.98  num_of_sem_filtered_clauses:            1
% 3.68/0.98  num_of_subtypes:                        0
% 3.68/0.98  monotx_restored_types:                  0
% 3.68/0.98  sat_num_of_epr_types:                   0
% 3.68/0.98  sat_num_of_non_cyclic_types:            0
% 3.68/0.98  sat_guarded_non_collapsed_types:        0
% 3.68/0.98  num_pure_diseq_elim:                    0
% 3.68/0.98  simp_replaced_by:                       0
% 3.68/0.98  res_preprocessed:                       94
% 3.68/0.98  prep_upred:                             0
% 3.68/0.98  prep_unflattend:                        15
% 3.68/0.98  smt_new_axioms:                         0
% 3.68/0.98  pred_elim_cands:                        3
% 3.68/0.98  pred_elim:                              4
% 3.68/0.98  pred_elim_cl:                           5
% 3.68/0.98  pred_elim_cycles:                       6
% 3.68/0.98  merged_defs:                            8
% 3.68/0.98  merged_defs_ncl:                        0
% 3.68/0.98  bin_hyper_res:                          10
% 3.68/0.98  prep_cycles:                            4
% 3.68/0.98  pred_elim_time:                         0.007
% 3.68/0.98  splitting_time:                         0.
% 3.68/0.98  sem_filter_time:                        0.
% 3.68/0.98  monotx_time:                            0.
% 3.68/0.98  subtype_inf_time:                       0.
% 3.68/0.98  
% 3.68/0.98  ------ Problem properties
% 3.68/0.98  
% 3.68/0.98  clauses:                                17
% 3.68/0.98  conjectures:                            4
% 3.68/0.98  epr:                                    0
% 3.68/0.98  horn:                                   13
% 3.68/0.98  ground:                                 5
% 3.68/0.98  unary:                                  1
% 3.68/0.98  binary:                                 10
% 3.68/0.98  lits:                                   44
% 3.68/0.98  lits_eq:                                5
% 3.68/0.98  fd_pure:                                0
% 3.68/0.98  fd_pseudo:                              0
% 3.68/0.98  fd_cond:                                0
% 3.68/0.98  fd_pseudo_cond:                         0
% 3.68/0.98  ac_symbols:                             0
% 3.68/0.98  
% 3.68/0.98  ------ Propositional Solver
% 3.68/0.98  
% 3.68/0.98  prop_solver_calls:                      30
% 3.68/0.98  prop_fast_solver_calls:                 823
% 3.68/0.98  smt_solver_calls:                       0
% 3.68/0.98  smt_fast_solver_calls:                  0
% 3.68/0.98  prop_num_of_clauses:                    4257
% 3.68/0.98  prop_preprocess_simplified:             8321
% 3.68/0.98  prop_fo_subsumed:                       26
% 3.68/0.98  prop_solver_time:                       0.
% 3.68/0.98  smt_solver_time:                        0.
% 3.68/0.98  smt_fast_solver_time:                   0.
% 3.68/0.98  prop_fast_solver_time:                  0.
% 3.68/0.98  prop_unsat_core_time:                   0.
% 3.68/0.98  
% 3.68/0.98  ------ QBF
% 3.68/0.98  
% 3.68/0.98  qbf_q_res:                              0
% 3.68/0.98  qbf_num_tautologies:                    0
% 3.68/0.98  qbf_prep_cycles:                        0
% 3.68/0.98  
% 3.68/0.98  ------ BMC1
% 3.68/0.98  
% 3.68/0.98  bmc1_current_bound:                     -1
% 3.68/0.98  bmc1_last_solved_bound:                 -1
% 3.68/0.98  bmc1_unsat_core_size:                   -1
% 3.68/0.98  bmc1_unsat_core_parents_size:           -1
% 3.68/0.98  bmc1_merge_next_fun:                    0
% 3.68/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation
% 3.68/0.98  
% 3.68/0.98  inst_num_of_clauses:                    1453
% 3.68/0.98  inst_num_in_passive:                    487
% 3.68/0.98  inst_num_in_active:                     415
% 3.68/0.98  inst_num_in_unprocessed:                551
% 3.68/0.98  inst_num_of_loops:                      480
% 3.68/0.98  inst_num_of_learning_restarts:          0
% 3.68/0.98  inst_num_moves_active_passive:          63
% 3.68/0.98  inst_lit_activity:                      0
% 3.68/0.98  inst_lit_activity_moves:                1
% 3.68/0.98  inst_num_tautologies:                   0
% 3.68/0.98  inst_num_prop_implied:                  0
% 3.68/0.98  inst_num_existing_simplified:           0
% 3.68/0.98  inst_num_eq_res_simplified:             0
% 3.68/0.98  inst_num_child_elim:                    0
% 3.68/0.98  inst_num_of_dismatching_blockings:      292
% 3.68/0.98  inst_num_of_non_proper_insts:           1305
% 3.68/0.98  inst_num_of_duplicates:                 0
% 3.68/0.98  inst_inst_num_from_inst_to_res:         0
% 3.68/0.98  inst_dismatching_checking_time:         0.
% 3.68/0.98  
% 3.68/0.98  ------ Resolution
% 3.68/0.98  
% 3.68/0.98  res_num_of_clauses:                     0
% 3.68/0.98  res_num_in_passive:                     0
% 3.68/0.98  res_num_in_active:                      0
% 3.68/0.98  res_num_of_loops:                       98
% 3.68/0.98  res_forward_subset_subsumed:            43
% 3.68/0.98  res_backward_subset_subsumed:           0
% 3.68/0.98  res_forward_subsumed:                   0
% 3.68/0.98  res_backward_subsumed:                  0
% 3.68/0.98  res_forward_subsumption_resolution:     0
% 3.68/0.98  res_backward_subsumption_resolution:    0
% 3.68/0.98  res_clause_to_clause_subsumption:       749
% 3.68/0.98  res_orphan_elimination:                 0
% 3.68/0.98  res_tautology_del:                      56
% 3.68/0.98  res_num_eq_res_simplified:              0
% 3.68/0.98  res_num_sel_changes:                    0
% 3.68/0.98  res_moves_from_active_to_pass:          0
% 3.68/0.98  
% 3.68/0.98  ------ Superposition
% 3.68/0.98  
% 3.68/0.98  sup_time_total:                         0.
% 3.68/0.98  sup_time_generating:                    0.
% 3.68/0.98  sup_time_sim_full:                      0.
% 3.68/0.98  sup_time_sim_immed:                     0.
% 3.68/0.98  
% 3.68/0.98  sup_num_of_clauses:                     184
% 3.68/0.98  sup_num_in_active:                      92
% 3.68/0.98  sup_num_in_passive:                     92
% 3.68/0.98  sup_num_of_loops:                       94
% 3.68/0.98  sup_fw_superposition:                   268
% 3.68/0.98  sup_bw_superposition:                   50
% 3.68/0.98  sup_immediate_simplified:               66
% 3.68/0.98  sup_given_eliminated:                   0
% 3.68/0.98  comparisons_done:                       0
% 3.68/0.98  comparisons_avoided:                    0
% 3.68/0.98  
% 3.68/0.98  ------ Simplifications
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  sim_fw_subset_subsumed:                 22
% 3.68/0.98  sim_bw_subset_subsumed:                 3
% 3.68/0.98  sim_fw_subsumed:                        5
% 3.68/0.98  sim_bw_subsumed:                        0
% 3.68/0.98  sim_fw_subsumption_res:                 0
% 3.68/0.98  sim_bw_subsumption_res:                 0
% 3.68/0.98  sim_tautology_del:                      6
% 3.68/0.98  sim_eq_tautology_del:                   23
% 3.68/0.98  sim_eq_res_simp:                        0
% 3.68/0.98  sim_fw_demodulated:                     0
% 3.68/0.98  sim_bw_demodulated:                     1
% 3.68/0.98  sim_light_normalised:                   48
% 3.68/0.98  sim_joinable_taut:                      0
% 3.68/0.98  sim_joinable_simp:                      0
% 3.68/0.98  sim_ac_normalised:                      0
% 3.68/0.98  sim_smt_subsumption:                    0
% 3.68/0.98  
%------------------------------------------------------------------------------
