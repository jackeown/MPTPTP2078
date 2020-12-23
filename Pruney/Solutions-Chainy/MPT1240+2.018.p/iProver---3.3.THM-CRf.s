%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:01 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  163 (2114 expanded)
%              Number of clauses        :   97 ( 519 expanded)
%              Number of leaves         :   17 ( 519 expanded)
%              Depth                    :   34
%              Number of atoms          :  576 (18248 expanded)
%              Number of equality atoms :  122 ( 370 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

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

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1335,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_465,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_466,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_411,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_412,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_544,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) = X1
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_466,c_412])).

cnf(c_545,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_19,negated_conjecture,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_596,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | sK3 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_545,c_19])).

cnf(c_597,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_599,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_597,c_20])).

cnf(c_600,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(renaming,[status(thm)],[c_599])).

cnf(c_1327,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_14,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_399,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_400,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_1411,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_16,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,sK2)
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_11,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_353,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_354,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_22])).

cnf(c_359,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_636,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_359])).

cnf(c_637,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_641,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_637,c_442])).

cnf(c_642,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_641])).

cnf(c_1492,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1518,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1836,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1518])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_188,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_238,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_188])).

cnf(c_1529,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_2081,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_2880,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1327,c_21,c_20,c_600,c_1411,c_1492,c_1836,c_2081])).

cnf(c_1336,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1412,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_1493,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1492])).

cnf(c_1557,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1336,c_26,c_27,c_1412,c_1493])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_1330,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_2365,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_1557,c_1330])).

cnf(c_2882,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_2880,c_2365])).

cnf(c_1341,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1869,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1341])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_239,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_188])).

cnf(c_1333,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_2654,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1869,c_1333])).

cnf(c_2883,plain,
    ( k1_tops_1(sK0,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2882,c_2654])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_480,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_481,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_1329,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_6478,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2883,c_1329])).

cnf(c_7517,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6478,c_26,c_27,c_1412,c_1493])).

cnf(c_7518,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7517])).

cnf(c_7526,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_7518])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( r1_tarski(sK3,sK2) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7743,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7526,c_26,c_29,c_1412,c_1493])).

cnf(c_1342,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1340,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2579,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_1340])).

cnf(c_7747,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_2579])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1343,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8240,plain,
    ( r2_hidden(X0,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v1_xboole_0(k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7747,c_1343])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1339,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2114,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_1339])).

cnf(c_7748,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | v1_xboole_0(k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7743,c_2114])).

cnf(c_9379,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8240,c_7748])).

cnf(c_9380,plain,
    ( r2_hidden(X0,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_9379])).

cnf(c_1325,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),sK2) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,X0)) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_1862,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1325,c_26,c_1412,c_1493])).

cnf(c_9385,plain,
    ( r2_hidden(sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9380,c_1862])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9385,c_1493,c_1412,c_30,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.98/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.02  
% 3.98/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.98/1.02  
% 3.98/1.02  ------  iProver source info
% 3.98/1.02  
% 3.98/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.98/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.98/1.02  git: non_committed_changes: false
% 3.98/1.02  git: last_make_outside_of_git: false
% 3.98/1.02  
% 3.98/1.02  ------ 
% 3.98/1.02  
% 3.98/1.02  ------ Input Options
% 3.98/1.02  
% 3.98/1.02  --out_options                           all
% 3.98/1.02  --tptp_safe_out                         true
% 3.98/1.02  --problem_path                          ""
% 3.98/1.02  --include_path                          ""
% 3.98/1.02  --clausifier                            res/vclausify_rel
% 3.98/1.02  --clausifier_options                    ""
% 3.98/1.02  --stdin                                 false
% 3.98/1.02  --stats_out                             all
% 3.98/1.02  
% 3.98/1.02  ------ General Options
% 3.98/1.02  
% 3.98/1.02  --fof                                   false
% 3.98/1.02  --time_out_real                         305.
% 3.98/1.02  --time_out_virtual                      -1.
% 3.98/1.02  --symbol_type_check                     false
% 3.98/1.02  --clausify_out                          false
% 3.98/1.02  --sig_cnt_out                           false
% 3.98/1.02  --trig_cnt_out                          false
% 3.98/1.02  --trig_cnt_out_tolerance                1.
% 3.98/1.02  --trig_cnt_out_sk_spl                   false
% 3.98/1.02  --abstr_cl_out                          false
% 3.98/1.02  
% 3.98/1.02  ------ Global Options
% 3.98/1.02  
% 3.98/1.02  --schedule                              default
% 3.98/1.02  --add_important_lit                     false
% 3.98/1.02  --prop_solver_per_cl                    1000
% 3.98/1.02  --min_unsat_core                        false
% 3.98/1.02  --soft_assumptions                      false
% 3.98/1.02  --soft_lemma_size                       3
% 3.98/1.02  --prop_impl_unit_size                   0
% 3.98/1.02  --prop_impl_unit                        []
% 3.98/1.02  --share_sel_clauses                     true
% 3.98/1.02  --reset_solvers                         false
% 3.98/1.02  --bc_imp_inh                            [conj_cone]
% 3.98/1.02  --conj_cone_tolerance                   3.
% 3.98/1.02  --extra_neg_conj                        none
% 3.98/1.02  --large_theory_mode                     true
% 3.98/1.02  --prolific_symb_bound                   200
% 3.98/1.02  --lt_threshold                          2000
% 3.98/1.02  --clause_weak_htbl                      true
% 3.98/1.02  --gc_record_bc_elim                     false
% 3.98/1.02  
% 3.98/1.02  ------ Preprocessing Options
% 3.98/1.02  
% 3.98/1.02  --preprocessing_flag                    true
% 3.98/1.02  --time_out_prep_mult                    0.1
% 3.98/1.02  --splitting_mode                        input
% 3.98/1.02  --splitting_grd                         true
% 3.98/1.02  --splitting_cvd                         false
% 3.98/1.02  --splitting_cvd_svl                     false
% 3.98/1.02  --splitting_nvd                         32
% 3.98/1.02  --sub_typing                            true
% 3.98/1.02  --prep_gs_sim                           true
% 3.98/1.02  --prep_unflatten                        true
% 3.98/1.02  --prep_res_sim                          true
% 3.98/1.02  --prep_upred                            true
% 3.98/1.02  --prep_sem_filter                       exhaustive
% 3.98/1.02  --prep_sem_filter_out                   false
% 3.98/1.02  --pred_elim                             true
% 3.98/1.02  --res_sim_input                         true
% 3.98/1.02  --eq_ax_congr_red                       true
% 3.98/1.02  --pure_diseq_elim                       true
% 3.98/1.02  --brand_transform                       false
% 3.98/1.02  --non_eq_to_eq                          false
% 3.98/1.02  --prep_def_merge                        true
% 3.98/1.02  --prep_def_merge_prop_impl              false
% 3.98/1.02  --prep_def_merge_mbd                    true
% 3.98/1.02  --prep_def_merge_tr_red                 false
% 3.98/1.02  --prep_def_merge_tr_cl                  false
% 3.98/1.02  --smt_preprocessing                     true
% 3.98/1.02  --smt_ac_axioms                         fast
% 3.98/1.02  --preprocessed_out                      false
% 3.98/1.02  --preprocessed_stats                    false
% 3.98/1.02  
% 3.98/1.02  ------ Abstraction refinement Options
% 3.98/1.02  
% 3.98/1.02  --abstr_ref                             []
% 3.98/1.02  --abstr_ref_prep                        false
% 3.98/1.02  --abstr_ref_until_sat                   false
% 3.98/1.02  --abstr_ref_sig_restrict                funpre
% 3.98/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.98/1.02  --abstr_ref_under                       []
% 3.98/1.02  
% 3.98/1.02  ------ SAT Options
% 3.98/1.02  
% 3.98/1.02  --sat_mode                              false
% 3.98/1.02  --sat_fm_restart_options                ""
% 3.98/1.02  --sat_gr_def                            false
% 3.98/1.02  --sat_epr_types                         true
% 3.98/1.02  --sat_non_cyclic_types                  false
% 3.98/1.02  --sat_finite_models                     false
% 3.98/1.02  --sat_fm_lemmas                         false
% 3.98/1.02  --sat_fm_prep                           false
% 3.98/1.02  --sat_fm_uc_incr                        true
% 3.98/1.02  --sat_out_model                         small
% 3.98/1.02  --sat_out_clauses                       false
% 3.98/1.02  
% 3.98/1.02  ------ QBF Options
% 3.98/1.02  
% 3.98/1.02  --qbf_mode                              false
% 3.98/1.02  --qbf_elim_univ                         false
% 3.98/1.02  --qbf_dom_inst                          none
% 3.98/1.02  --qbf_dom_pre_inst                      false
% 3.98/1.02  --qbf_sk_in                             false
% 3.98/1.02  --qbf_pred_elim                         true
% 3.98/1.02  --qbf_split                             512
% 3.98/1.02  
% 3.98/1.02  ------ BMC1 Options
% 3.98/1.02  
% 3.98/1.02  --bmc1_incremental                      false
% 3.98/1.02  --bmc1_axioms                           reachable_all
% 3.98/1.02  --bmc1_min_bound                        0
% 3.98/1.02  --bmc1_max_bound                        -1
% 3.98/1.02  --bmc1_max_bound_default                -1
% 3.98/1.02  --bmc1_symbol_reachability              true
% 3.98/1.02  --bmc1_property_lemmas                  false
% 3.98/1.02  --bmc1_k_induction                      false
% 3.98/1.02  --bmc1_non_equiv_states                 false
% 3.98/1.02  --bmc1_deadlock                         false
% 3.98/1.02  --bmc1_ucm                              false
% 3.98/1.02  --bmc1_add_unsat_core                   none
% 3.98/1.02  --bmc1_unsat_core_children              false
% 3.98/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.98/1.02  --bmc1_out_stat                         full
% 3.98/1.02  --bmc1_ground_init                      false
% 3.98/1.02  --bmc1_pre_inst_next_state              false
% 3.98/1.02  --bmc1_pre_inst_state                   false
% 3.98/1.02  --bmc1_pre_inst_reach_state             false
% 3.98/1.02  --bmc1_out_unsat_core                   false
% 3.98/1.02  --bmc1_aig_witness_out                  false
% 3.98/1.02  --bmc1_verbose                          false
% 3.98/1.02  --bmc1_dump_clauses_tptp                false
% 3.98/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.98/1.02  --bmc1_dump_file                        -
% 3.98/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.98/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.98/1.02  --bmc1_ucm_extend_mode                  1
% 3.98/1.02  --bmc1_ucm_init_mode                    2
% 3.98/1.02  --bmc1_ucm_cone_mode                    none
% 3.98/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.98/1.02  --bmc1_ucm_relax_model                  4
% 3.98/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.98/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.98/1.02  --bmc1_ucm_layered_model                none
% 3.98/1.02  --bmc1_ucm_max_lemma_size               10
% 3.98/1.02  
% 3.98/1.02  ------ AIG Options
% 3.98/1.02  
% 3.98/1.02  --aig_mode                              false
% 3.98/1.02  
% 3.98/1.02  ------ Instantiation Options
% 3.98/1.02  
% 3.98/1.02  --instantiation_flag                    true
% 3.98/1.02  --inst_sos_flag                         true
% 3.98/1.02  --inst_sos_phase                        true
% 3.98/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.98/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.98/1.02  --inst_lit_sel_side                     num_symb
% 3.98/1.02  --inst_solver_per_active                1400
% 3.98/1.02  --inst_solver_calls_frac                1.
% 3.98/1.02  --inst_passive_queue_type               priority_queues
% 3.98/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.98/1.02  --inst_passive_queues_freq              [25;2]
% 3.98/1.02  --inst_dismatching                      true
% 3.98/1.02  --inst_eager_unprocessed_to_passive     true
% 3.98/1.02  --inst_prop_sim_given                   true
% 3.98/1.02  --inst_prop_sim_new                     false
% 3.98/1.02  --inst_subs_new                         false
% 3.98/1.02  --inst_eq_res_simp                      false
% 3.98/1.02  --inst_subs_given                       false
% 3.98/1.02  --inst_orphan_elimination               true
% 3.98/1.02  --inst_learning_loop_flag               true
% 3.98/1.02  --inst_learning_start                   3000
% 3.98/1.02  --inst_learning_factor                  2
% 3.98/1.02  --inst_start_prop_sim_after_learn       3
% 3.98/1.02  --inst_sel_renew                        solver
% 3.98/1.02  --inst_lit_activity_flag                true
% 3.98/1.02  --inst_restr_to_given                   false
% 3.98/1.02  --inst_activity_threshold               500
% 3.98/1.02  --inst_out_proof                        true
% 3.98/1.02  
% 3.98/1.02  ------ Resolution Options
% 3.98/1.02  
% 3.98/1.02  --resolution_flag                       true
% 3.98/1.02  --res_lit_sel                           adaptive
% 3.98/1.02  --res_lit_sel_side                      none
% 3.98/1.02  --res_ordering                          kbo
% 3.98/1.02  --res_to_prop_solver                    active
% 3.98/1.02  --res_prop_simpl_new                    false
% 3.98/1.02  --res_prop_simpl_given                  true
% 3.98/1.02  --res_passive_queue_type                priority_queues
% 3.98/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.98/1.02  --res_passive_queues_freq               [15;5]
% 3.98/1.02  --res_forward_subs                      full
% 3.98/1.02  --res_backward_subs                     full
% 3.98/1.02  --res_forward_subs_resolution           true
% 3.98/1.02  --res_backward_subs_resolution          true
% 3.98/1.02  --res_orphan_elimination                true
% 3.98/1.02  --res_time_limit                        2.
% 3.98/1.02  --res_out_proof                         true
% 3.98/1.02  
% 3.98/1.02  ------ Superposition Options
% 3.98/1.02  
% 3.98/1.02  --superposition_flag                    true
% 3.98/1.02  --sup_passive_queue_type                priority_queues
% 3.98/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.98/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.98/1.02  --demod_completeness_check              fast
% 3.98/1.02  --demod_use_ground                      true
% 3.98/1.02  --sup_to_prop_solver                    passive
% 3.98/1.02  --sup_prop_simpl_new                    true
% 3.98/1.02  --sup_prop_simpl_given                  true
% 3.98/1.02  --sup_fun_splitting                     true
% 3.98/1.02  --sup_smt_interval                      50000
% 3.98/1.02  
% 3.98/1.02  ------ Superposition Simplification Setup
% 3.98/1.02  
% 3.98/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.98/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.98/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.98/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.98/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.98/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.98/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.98/1.02  --sup_immed_triv                        [TrivRules]
% 3.98/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.02  --sup_immed_bw_main                     []
% 3.98/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.98/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.98/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.02  --sup_input_bw                          []
% 3.98/1.02  
% 3.98/1.02  ------ Combination Options
% 3.98/1.02  
% 3.98/1.02  --comb_res_mult                         3
% 3.98/1.02  --comb_sup_mult                         2
% 3.98/1.02  --comb_inst_mult                        10
% 3.98/1.02  
% 3.98/1.02  ------ Debug Options
% 3.98/1.02  
% 3.98/1.02  --dbg_backtrace                         false
% 3.98/1.02  --dbg_dump_prop_clauses                 false
% 3.98/1.02  --dbg_dump_prop_clauses_file            -
% 3.98/1.02  --dbg_out_stat                          false
% 3.98/1.02  ------ Parsing...
% 3.98/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.98/1.02  
% 3.98/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.98/1.02  
% 3.98/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.98/1.02  
% 3.98/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.98/1.02  ------ Proving...
% 3.98/1.02  ------ Problem Properties 
% 3.98/1.02  
% 3.98/1.02  
% 3.98/1.02  clauses                                 19
% 3.98/1.02  conjectures                             4
% 3.98/1.02  EPR                                     1
% 3.98/1.02  Horn                                    14
% 3.98/1.02  unary                                   1
% 3.98/1.02  binary                                  10
% 3.98/1.02  lits                                    50
% 3.98/1.02  lits eq                                 5
% 3.98/1.02  fd_pure                                 0
% 3.98/1.02  fd_pseudo                               0
% 3.98/1.02  fd_cond                                 0
% 3.98/1.02  fd_pseudo_cond                          0
% 3.98/1.02  AC symbols                              0
% 3.98/1.02  
% 3.98/1.02  ------ Schedule dynamic 5 is on 
% 3.98/1.02  
% 3.98/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.98/1.02  
% 3.98/1.02  
% 3.98/1.02  ------ 
% 3.98/1.02  Current options:
% 3.98/1.02  ------ 
% 3.98/1.02  
% 3.98/1.02  ------ Input Options
% 3.98/1.02  
% 3.98/1.02  --out_options                           all
% 3.98/1.02  --tptp_safe_out                         true
% 3.98/1.02  --problem_path                          ""
% 3.98/1.02  --include_path                          ""
% 3.98/1.02  --clausifier                            res/vclausify_rel
% 3.98/1.02  --clausifier_options                    ""
% 3.98/1.02  --stdin                                 false
% 3.98/1.02  --stats_out                             all
% 3.98/1.02  
% 3.98/1.02  ------ General Options
% 3.98/1.02  
% 3.98/1.02  --fof                                   false
% 3.98/1.02  --time_out_real                         305.
% 3.98/1.02  --time_out_virtual                      -1.
% 3.98/1.02  --symbol_type_check                     false
% 3.98/1.02  --clausify_out                          false
% 3.98/1.02  --sig_cnt_out                           false
% 3.98/1.02  --trig_cnt_out                          false
% 3.98/1.02  --trig_cnt_out_tolerance                1.
% 3.98/1.02  --trig_cnt_out_sk_spl                   false
% 3.98/1.02  --abstr_cl_out                          false
% 3.98/1.02  
% 3.98/1.02  ------ Global Options
% 3.98/1.02  
% 3.98/1.02  --schedule                              default
% 3.98/1.02  --add_important_lit                     false
% 3.98/1.02  --prop_solver_per_cl                    1000
% 3.98/1.02  --min_unsat_core                        false
% 3.98/1.02  --soft_assumptions                      false
% 3.98/1.02  --soft_lemma_size                       3
% 3.98/1.02  --prop_impl_unit_size                   0
% 3.98/1.02  --prop_impl_unit                        []
% 3.98/1.02  --share_sel_clauses                     true
% 3.98/1.02  --reset_solvers                         false
% 3.98/1.02  --bc_imp_inh                            [conj_cone]
% 3.98/1.02  --conj_cone_tolerance                   3.
% 3.98/1.02  --extra_neg_conj                        none
% 3.98/1.02  --large_theory_mode                     true
% 3.98/1.02  --prolific_symb_bound                   200
% 3.98/1.02  --lt_threshold                          2000
% 3.98/1.02  --clause_weak_htbl                      true
% 3.98/1.02  --gc_record_bc_elim                     false
% 3.98/1.02  
% 3.98/1.02  ------ Preprocessing Options
% 3.98/1.02  
% 3.98/1.02  --preprocessing_flag                    true
% 3.98/1.02  --time_out_prep_mult                    0.1
% 3.98/1.02  --splitting_mode                        input
% 3.98/1.02  --splitting_grd                         true
% 3.98/1.02  --splitting_cvd                         false
% 3.98/1.02  --splitting_cvd_svl                     false
% 3.98/1.02  --splitting_nvd                         32
% 3.98/1.02  --sub_typing                            true
% 3.98/1.02  --prep_gs_sim                           true
% 3.98/1.02  --prep_unflatten                        true
% 3.98/1.02  --prep_res_sim                          true
% 3.98/1.02  --prep_upred                            true
% 3.98/1.02  --prep_sem_filter                       exhaustive
% 3.98/1.02  --prep_sem_filter_out                   false
% 3.98/1.02  --pred_elim                             true
% 3.98/1.02  --res_sim_input                         true
% 3.98/1.02  --eq_ax_congr_red                       true
% 3.98/1.02  --pure_diseq_elim                       true
% 3.98/1.02  --brand_transform                       false
% 3.98/1.02  --non_eq_to_eq                          false
% 3.98/1.02  --prep_def_merge                        true
% 3.98/1.02  --prep_def_merge_prop_impl              false
% 3.98/1.02  --prep_def_merge_mbd                    true
% 3.98/1.02  --prep_def_merge_tr_red                 false
% 3.98/1.02  --prep_def_merge_tr_cl                  false
% 3.98/1.02  --smt_preprocessing                     true
% 3.98/1.02  --smt_ac_axioms                         fast
% 3.98/1.02  --preprocessed_out                      false
% 3.98/1.02  --preprocessed_stats                    false
% 3.98/1.02  
% 3.98/1.02  ------ Abstraction refinement Options
% 3.98/1.02  
% 3.98/1.02  --abstr_ref                             []
% 3.98/1.02  --abstr_ref_prep                        false
% 3.98/1.02  --abstr_ref_until_sat                   false
% 3.98/1.02  --abstr_ref_sig_restrict                funpre
% 3.98/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.98/1.02  --abstr_ref_under                       []
% 3.98/1.02  
% 3.98/1.02  ------ SAT Options
% 3.98/1.02  
% 3.98/1.02  --sat_mode                              false
% 3.98/1.02  --sat_fm_restart_options                ""
% 3.98/1.02  --sat_gr_def                            false
% 3.98/1.02  --sat_epr_types                         true
% 3.98/1.02  --sat_non_cyclic_types                  false
% 3.98/1.02  --sat_finite_models                     false
% 3.98/1.02  --sat_fm_lemmas                         false
% 3.98/1.02  --sat_fm_prep                           false
% 3.98/1.02  --sat_fm_uc_incr                        true
% 3.98/1.02  --sat_out_model                         small
% 3.98/1.02  --sat_out_clauses                       false
% 3.98/1.02  
% 3.98/1.02  ------ QBF Options
% 3.98/1.02  
% 3.98/1.02  --qbf_mode                              false
% 3.98/1.02  --qbf_elim_univ                         false
% 3.98/1.02  --qbf_dom_inst                          none
% 3.98/1.02  --qbf_dom_pre_inst                      false
% 3.98/1.02  --qbf_sk_in                             false
% 3.98/1.02  --qbf_pred_elim                         true
% 3.98/1.02  --qbf_split                             512
% 3.98/1.02  
% 3.98/1.02  ------ BMC1 Options
% 3.98/1.02  
% 3.98/1.02  --bmc1_incremental                      false
% 3.98/1.02  --bmc1_axioms                           reachable_all
% 3.98/1.02  --bmc1_min_bound                        0
% 3.98/1.02  --bmc1_max_bound                        -1
% 3.98/1.02  --bmc1_max_bound_default                -1
% 3.98/1.02  --bmc1_symbol_reachability              true
% 3.98/1.02  --bmc1_property_lemmas                  false
% 3.98/1.02  --bmc1_k_induction                      false
% 3.98/1.02  --bmc1_non_equiv_states                 false
% 3.98/1.02  --bmc1_deadlock                         false
% 3.98/1.02  --bmc1_ucm                              false
% 3.98/1.02  --bmc1_add_unsat_core                   none
% 3.98/1.02  --bmc1_unsat_core_children              false
% 3.98/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.98/1.02  --bmc1_out_stat                         full
% 3.98/1.02  --bmc1_ground_init                      false
% 3.98/1.02  --bmc1_pre_inst_next_state              false
% 3.98/1.02  --bmc1_pre_inst_state                   false
% 3.98/1.02  --bmc1_pre_inst_reach_state             false
% 3.98/1.02  --bmc1_out_unsat_core                   false
% 3.98/1.02  --bmc1_aig_witness_out                  false
% 3.98/1.02  --bmc1_verbose                          false
% 3.98/1.02  --bmc1_dump_clauses_tptp                false
% 3.98/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.98/1.02  --bmc1_dump_file                        -
% 3.98/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.98/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.98/1.02  --bmc1_ucm_extend_mode                  1
% 3.98/1.02  --bmc1_ucm_init_mode                    2
% 3.98/1.02  --bmc1_ucm_cone_mode                    none
% 3.98/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.98/1.02  --bmc1_ucm_relax_model                  4
% 3.98/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.98/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.98/1.02  --bmc1_ucm_layered_model                none
% 3.98/1.02  --bmc1_ucm_max_lemma_size               10
% 3.98/1.02  
% 3.98/1.02  ------ AIG Options
% 3.98/1.02  
% 3.98/1.02  --aig_mode                              false
% 3.98/1.02  
% 3.98/1.02  ------ Instantiation Options
% 3.98/1.02  
% 3.98/1.02  --instantiation_flag                    true
% 3.98/1.02  --inst_sos_flag                         true
% 3.98/1.02  --inst_sos_phase                        true
% 3.98/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.98/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.98/1.02  --inst_lit_sel_side                     none
% 3.98/1.02  --inst_solver_per_active                1400
% 3.98/1.02  --inst_solver_calls_frac                1.
% 3.98/1.02  --inst_passive_queue_type               priority_queues
% 3.98/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.98/1.02  --inst_passive_queues_freq              [25;2]
% 3.98/1.02  --inst_dismatching                      true
% 3.98/1.02  --inst_eager_unprocessed_to_passive     true
% 3.98/1.02  --inst_prop_sim_given                   true
% 3.98/1.02  --inst_prop_sim_new                     false
% 3.98/1.02  --inst_subs_new                         false
% 3.98/1.02  --inst_eq_res_simp                      false
% 3.98/1.02  --inst_subs_given                       false
% 3.98/1.02  --inst_orphan_elimination               true
% 3.98/1.02  --inst_learning_loop_flag               true
% 3.98/1.02  --inst_learning_start                   3000
% 3.98/1.02  --inst_learning_factor                  2
% 3.98/1.02  --inst_start_prop_sim_after_learn       3
% 3.98/1.02  --inst_sel_renew                        solver
% 3.98/1.02  --inst_lit_activity_flag                true
% 3.98/1.02  --inst_restr_to_given                   false
% 3.98/1.02  --inst_activity_threshold               500
% 3.98/1.02  --inst_out_proof                        true
% 3.98/1.02  
% 3.98/1.02  ------ Resolution Options
% 3.98/1.02  
% 3.98/1.02  --resolution_flag                       false
% 3.98/1.02  --res_lit_sel                           adaptive
% 3.98/1.02  --res_lit_sel_side                      none
% 3.98/1.02  --res_ordering                          kbo
% 3.98/1.02  --res_to_prop_solver                    active
% 3.98/1.02  --res_prop_simpl_new                    false
% 3.98/1.02  --res_prop_simpl_given                  true
% 3.98/1.02  --res_passive_queue_type                priority_queues
% 3.98/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.98/1.02  --res_passive_queues_freq               [15;5]
% 3.98/1.02  --res_forward_subs                      full
% 3.98/1.02  --res_backward_subs                     full
% 3.98/1.02  --res_forward_subs_resolution           true
% 3.98/1.02  --res_backward_subs_resolution          true
% 3.98/1.02  --res_orphan_elimination                true
% 3.98/1.02  --res_time_limit                        2.
% 3.98/1.02  --res_out_proof                         true
% 3.98/1.02  
% 3.98/1.02  ------ Superposition Options
% 3.98/1.02  
% 3.98/1.02  --superposition_flag                    true
% 3.98/1.02  --sup_passive_queue_type                priority_queues
% 3.98/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.98/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.98/1.02  --demod_completeness_check              fast
% 3.98/1.02  --demod_use_ground                      true
% 3.98/1.02  --sup_to_prop_solver                    passive
% 3.98/1.02  --sup_prop_simpl_new                    true
% 3.98/1.02  --sup_prop_simpl_given                  true
% 3.98/1.02  --sup_fun_splitting                     true
% 3.98/1.02  --sup_smt_interval                      50000
% 3.98/1.02  
% 3.98/1.02  ------ Superposition Simplification Setup
% 3.98/1.02  
% 3.98/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.98/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.98/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.98/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.98/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.98/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.98/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.98/1.02  --sup_immed_triv                        [TrivRules]
% 3.98/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.02  --sup_immed_bw_main                     []
% 3.98/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.98/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.98/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/1.02  --sup_input_bw                          []
% 3.98/1.02  
% 3.98/1.02  ------ Combination Options
% 3.98/1.02  
% 3.98/1.02  --comb_res_mult                         3
% 3.98/1.02  --comb_sup_mult                         2
% 3.98/1.02  --comb_inst_mult                        10
% 3.98/1.02  
% 3.98/1.02  ------ Debug Options
% 3.98/1.02  
% 3.98/1.02  --dbg_backtrace                         false
% 3.98/1.02  --dbg_dump_prop_clauses                 false
% 3.98/1.02  --dbg_dump_prop_clauses_file            -
% 3.98/1.02  --dbg_out_stat                          false
% 3.98/1.02  
% 3.98/1.02  
% 3.98/1.02  
% 3.98/1.02  
% 3.98/1.02  ------ Proving...
% 3.98/1.02  
% 3.98/1.02  
% 3.98/1.02  % SZS status Theorem for theBenchmark.p
% 3.98/1.02  
% 3.98/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.98/1.02  
% 3.98/1.02  fof(f14,conjecture,(
% 3.98/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f15,negated_conjecture,(
% 3.98/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.98/1.02    inference(negated_conjecture,[],[f14])).
% 3.98/1.02  
% 3.98/1.02  fof(f34,plain,(
% 3.98/1.02    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.98/1.02    inference(ennf_transformation,[],[f15])).
% 3.98/1.02  
% 3.98/1.02  fof(f35,plain,(
% 3.98/1.02    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.98/1.02    inference(flattening,[],[f34])).
% 3.98/1.02  
% 3.98/1.02  fof(f38,plain,(
% 3.98/1.02    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.98/1.02    inference(nnf_transformation,[],[f35])).
% 3.98/1.02  
% 3.98/1.02  fof(f39,plain,(
% 3.98/1.02    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.98/1.02    inference(flattening,[],[f38])).
% 3.98/1.02  
% 3.98/1.02  fof(f40,plain,(
% 3.98/1.02    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.98/1.02    inference(rectify,[],[f39])).
% 3.98/1.02  
% 3.98/1.02  fof(f43,plain,(
% 3.98/1.02    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3) & r1_tarski(sK3,X2) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.98/1.02    introduced(choice_axiom,[])).
% 3.98/1.02  
% 3.98/1.02  fof(f42,plain,(
% 3.98/1.02    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK1,k1_tops_1(X0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK1,k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.98/1.02    introduced(choice_axiom,[])).
% 3.98/1.02  
% 3.98/1.02  fof(f41,plain,(
% 3.98/1.02    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.98/1.02    introduced(choice_axiom,[])).
% 3.98/1.02  
% 3.98/1.02  fof(f44,plain,(
% 3.98/1.02    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.98/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f43,f42,f41])).
% 3.98/1.02  
% 3.98/1.02  fof(f63,plain,(
% 3.98/1.02    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.98/1.02    inference(cnf_transformation,[],[f44])).
% 3.98/1.02  
% 3.98/1.02  fof(f7,axiom,(
% 3.98/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f23,plain,(
% 3.98/1.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.98/1.02    inference(ennf_transformation,[],[f7])).
% 3.98/1.02  
% 3.98/1.02  fof(f24,plain,(
% 3.98/1.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.98/1.02    inference(flattening,[],[f23])).
% 3.98/1.02  
% 3.98/1.02  fof(f52,plain,(
% 3.98/1.02    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f24])).
% 3.98/1.02  
% 3.98/1.02  fof(f62,plain,(
% 3.98/1.02    l1_pre_topc(sK0)),
% 3.98/1.02    inference(cnf_transformation,[],[f44])).
% 3.98/1.02  
% 3.98/1.02  fof(f11,axiom,(
% 3.98/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f30,plain,(
% 3.98/1.02    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.98/1.02    inference(ennf_transformation,[],[f11])).
% 3.98/1.02  
% 3.98/1.02  fof(f37,plain,(
% 3.98/1.02    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.98/1.02    inference(nnf_transformation,[],[f30])).
% 3.98/1.02  
% 3.98/1.02  fof(f57,plain,(
% 3.98/1.02    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f37])).
% 3.98/1.02  
% 3.98/1.02  fof(f65,plain,(
% 3.98/1.02    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.98/1.02    inference(cnf_transformation,[],[f44])).
% 3.98/1.02  
% 3.98/1.02  fof(f64,plain,(
% 3.98/1.02    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.98/1.02    inference(cnf_transformation,[],[f44])).
% 3.98/1.02  
% 3.98/1.02  fof(f12,axiom,(
% 3.98/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f31,plain,(
% 3.98/1.02    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.98/1.02    inference(ennf_transformation,[],[f12])).
% 3.98/1.02  
% 3.98/1.02  fof(f59,plain,(
% 3.98/1.02    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f31])).
% 3.98/1.02  
% 3.98/1.02  fof(f68,plain,(
% 3.98/1.02    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 3.98/1.02    inference(cnf_transformation,[],[f44])).
% 3.98/1.02  
% 3.98/1.02  fof(f10,axiom,(
% 3.98/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f28,plain,(
% 3.98/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.98/1.02    inference(ennf_transformation,[],[f10])).
% 3.98/1.02  
% 3.98/1.02  fof(f29,plain,(
% 3.98/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.98/1.02    inference(flattening,[],[f28])).
% 3.98/1.02  
% 3.98/1.02  fof(f56,plain,(
% 3.98/1.02    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f29])).
% 3.98/1.02  
% 3.98/1.02  fof(f61,plain,(
% 3.98/1.02    v2_pre_topc(sK0)),
% 3.98/1.02    inference(cnf_transformation,[],[f44])).
% 3.98/1.02  
% 3.98/1.02  fof(f9,axiom,(
% 3.98/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f26,plain,(
% 3.98/1.02    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.98/1.02    inference(ennf_transformation,[],[f9])).
% 3.98/1.02  
% 3.98/1.02  fof(f27,plain,(
% 3.98/1.02    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.98/1.02    inference(flattening,[],[f26])).
% 3.98/1.02  
% 3.98/1.02  fof(f55,plain,(
% 3.98/1.02    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f27])).
% 3.98/1.02  
% 3.98/1.02  fof(f4,axiom,(
% 3.98/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f36,plain,(
% 3.98/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.98/1.02    inference(nnf_transformation,[],[f4])).
% 3.98/1.02  
% 3.98/1.02  fof(f48,plain,(
% 3.98/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.98/1.02    inference(cnf_transformation,[],[f36])).
% 3.98/1.02  
% 3.98/1.02  fof(f1,axiom,(
% 3.98/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f16,plain,(
% 3.98/1.02    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.98/1.02    inference(ennf_transformation,[],[f1])).
% 3.98/1.02  
% 3.98/1.02  fof(f45,plain,(
% 3.98/1.02    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.98/1.02    inference(cnf_transformation,[],[f16])).
% 3.98/1.02  
% 3.98/1.02  fof(f49,plain,(
% 3.98/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f36])).
% 3.98/1.02  
% 3.98/1.02  fof(f8,axiom,(
% 3.98/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f25,plain,(
% 3.98/1.02    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.98/1.02    inference(ennf_transformation,[],[f8])).
% 3.98/1.02  
% 3.98/1.02  fof(f54,plain,(
% 3.98/1.02    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f25])).
% 3.98/1.02  
% 3.98/1.02  fof(f2,axiom,(
% 3.98/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f17,plain,(
% 3.98/1.02    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.98/1.02    inference(ennf_transformation,[],[f2])).
% 3.98/1.02  
% 3.98/1.02  fof(f46,plain,(
% 3.98/1.02    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.98/1.02    inference(cnf_transformation,[],[f17])).
% 3.98/1.02  
% 3.98/1.02  fof(f13,axiom,(
% 3.98/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f32,plain,(
% 3.98/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.98/1.02    inference(ennf_transformation,[],[f13])).
% 3.98/1.02  
% 3.98/1.02  fof(f33,plain,(
% 3.98/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.98/1.02    inference(flattening,[],[f32])).
% 3.98/1.02  
% 3.98/1.02  fof(f60,plain,(
% 3.98/1.02    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f33])).
% 3.98/1.02  
% 3.98/1.02  fof(f66,plain,(
% 3.98/1.02    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.98/1.02    inference(cnf_transformation,[],[f44])).
% 3.98/1.02  
% 3.98/1.02  fof(f5,axiom,(
% 3.98/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f20,plain,(
% 3.98/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.98/1.02    inference(ennf_transformation,[],[f5])).
% 3.98/1.02  
% 3.98/1.02  fof(f21,plain,(
% 3.98/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.98/1.02    inference(flattening,[],[f20])).
% 3.98/1.02  
% 3.98/1.02  fof(f50,plain,(
% 3.98/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f21])).
% 3.98/1.02  
% 3.98/1.02  fof(f3,axiom,(
% 3.98/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f18,plain,(
% 3.98/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.98/1.02    inference(ennf_transformation,[],[f3])).
% 3.98/1.02  
% 3.98/1.02  fof(f19,plain,(
% 3.98/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.98/1.02    inference(flattening,[],[f18])).
% 3.98/1.02  
% 3.98/1.02  fof(f47,plain,(
% 3.98/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f19])).
% 3.98/1.02  
% 3.98/1.02  fof(f6,axiom,(
% 3.98/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.98/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/1.02  
% 3.98/1.02  fof(f22,plain,(
% 3.98/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.98/1.02    inference(ennf_transformation,[],[f6])).
% 3.98/1.02  
% 3.98/1.02  fof(f51,plain,(
% 3.98/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.98/1.02    inference(cnf_transformation,[],[f22])).
% 3.98/1.02  
% 3.98/1.02  fof(f67,plain,(
% 3.98/1.02    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 3.98/1.02    inference(cnf_transformation,[],[f44])).
% 3.98/1.02  
% 3.98/1.02  cnf(c_21,negated_conjecture,
% 3.98/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1335,plain,
% 3.98/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_8,plain,
% 3.98/1.02      ( ~ v4_pre_topc(X0,X1)
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.98/1.02      | ~ l1_pre_topc(X1)
% 3.98/1.02      | k2_pre_topc(X1,X0) = X0 ),
% 3.98/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_22,negated_conjecture,
% 3.98/1.02      ( l1_pre_topc(sK0) ),
% 3.98/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_465,plain,
% 3.98/1.02      ( ~ v4_pre_topc(X0,X1)
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.98/1.02      | k2_pre_topc(X1,X0) = X0
% 3.98/1.02      | sK0 != X1 ),
% 3.98/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_466,plain,
% 3.98/1.02      ( ~ v4_pre_topc(X0,sK0)
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | k2_pre_topc(sK0,X0) = X0 ),
% 3.98/1.02      inference(unflattening,[status(thm)],[c_465]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_13,plain,
% 3.98/1.02      ( ~ v3_pre_topc(X0,X1)
% 3.98/1.02      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.98/1.02      | ~ l1_pre_topc(X1) ),
% 3.98/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_411,plain,
% 3.98/1.02      ( ~ v3_pre_topc(X0,X1)
% 3.98/1.02      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.98/1.02      | sK0 != X1 ),
% 3.98/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_412,plain,
% 3.98/1.02      ( ~ v3_pre_topc(X0,sK0)
% 3.98/1.02      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(unflattening,[status(thm)],[c_411]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_544,plain,
% 3.98/1.02      ( ~ v3_pre_topc(X0,sK0)
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | k2_pre_topc(sK0,X1) = X1
% 3.98/1.02      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 3.98/1.02      | sK0 != sK0 ),
% 3.98/1.02      inference(resolution_lifted,[status(thm)],[c_466,c_412]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_545,plain,
% 3.98/1.02      ( ~ v3_pre_topc(X0,sK0)
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
% 3.98/1.02      inference(unflattening,[status(thm)],[c_544]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_19,negated_conjecture,
% 3.98/1.02      ( v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 3.98/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_596,plain,
% 3.98/1.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 3.98/1.02      | sK3 != X0
% 3.98/1.02      | sK0 != sK0 ),
% 3.98/1.02      inference(resolution_lifted,[status(thm)],[c_545,c_19]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_597,plain,
% 3.98/1.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.98/1.02      inference(unflattening,[status(thm)],[c_596]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_20,negated_conjecture,
% 3.98/1.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_599,plain,
% 3.98/1.02      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.98/1.02      inference(global_propositional_subsumption,
% 3.98/1.02                [status(thm)],
% 3.98/1.02                [c_597,c_20]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_600,plain,
% 3.98/1.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.98/1.02      inference(renaming,[status(thm)],[c_599]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1327,plain,
% 3.98/1.02      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
% 3.98/1.02      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.98/1.02      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_14,plain,
% 3.98/1.02      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.98/1.02      | ~ l1_pre_topc(X0) ),
% 3.98/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_399,plain,
% 3.98/1.02      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.98/1.02      | sK0 != X0 ),
% 3.98/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_400,plain,
% 3.98/1.02      ( r1_tarski(k1_tops_1(sK0,X0),X0)
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(unflattening,[status(thm)],[c_399]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1411,plain,
% 3.98/1.02      ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.98/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(instantiation,[status(thm)],[c_400]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_16,negated_conjecture,
% 3.98/1.02      ( ~ v3_pre_topc(X0,sK0)
% 3.98/1.02      | ~ r1_tarski(X0,sK2)
% 3.98/1.02      | ~ r2_hidden(sK1,X0)
% 3.98/1.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_11,plain,
% 3.98/1.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.98/1.02      | ~ l1_pre_topc(X0)
% 3.98/1.02      | ~ v2_pre_topc(X0) ),
% 3.98/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_23,negated_conjecture,
% 3.98/1.02      ( v2_pre_topc(sK0) ),
% 3.98/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_353,plain,
% 3.98/1.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.98/1.02      | ~ l1_pre_topc(X0)
% 3.98/1.02      | sK0 != X0 ),
% 3.98/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_354,plain,
% 3.98/1.02      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | ~ l1_pre_topc(sK0) ),
% 3.98/1.02      inference(unflattening,[status(thm)],[c_353]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_358,plain,
% 3.98/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 3.98/1.02      inference(global_propositional_subsumption,
% 3.98/1.02                [status(thm)],
% 3.98/1.02                [c_354,c_22]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_359,plain,
% 3.98/1.02      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(renaming,[status(thm)],[c_358]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_636,plain,
% 3.98/1.02      ( ~ r1_tarski(X0,sK2)
% 3.98/1.02      | ~ r2_hidden(sK1,X0)
% 3.98/1.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | k1_tops_1(sK0,X1) != X0
% 3.98/1.02      | sK0 != sK0 ),
% 3.98/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_359]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_637,plain,
% 3.98/1.02      ( ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
% 3.98/1.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.98/1.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(unflattening,[status(thm)],[c_636]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_10,plain,
% 3.98/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.98/1.02      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.98/1.02      | ~ l1_pre_topc(X1) ),
% 3.98/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_441,plain,
% 3.98/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.98/1.02      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.98/1.02      | sK0 != X1 ),
% 3.98/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_442,plain,
% 3.98/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(unflattening,[status(thm)],[c_441]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_641,plain,
% 3.98/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.98/1.02      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 3.98/1.02      inference(global_propositional_subsumption,
% 3.98/1.02                [status(thm)],
% 3.98/1.02                [c_637,c_442]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_642,plain,
% 3.98/1.02      ( ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
% 3.98/1.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.98/1.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(renaming,[status(thm)],[c_641]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1492,plain,
% 3.98/1.02      ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.98/1.02      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.98/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(instantiation,[status(thm)],[c_642]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_4,plain,
% 3.98/1.02      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.98/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1518,plain,
% 3.98/1.02      ( r1_tarski(X0,u1_struct_0(sK0))
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1836,plain,
% 3.98/1.02      ( r1_tarski(sK3,u1_struct_0(sK0))
% 3.98/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(instantiation,[status(thm)],[c_1518]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_0,plain,
% 3.98/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.98/1.02      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.98/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_3,plain,
% 3.98/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.98/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_188,plain,
% 3.98/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.98/1.02      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_238,plain,
% 3.98/1.02      ( ~ r1_tarski(X0,X1)
% 3.98/1.02      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.98/1.02      inference(bin_hyper_res,[status(thm)],[c_0,c_188]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1529,plain,
% 3.98/1.02      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 3.98/1.02      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(instantiation,[status(thm)],[c_238]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_2081,plain,
% 3.98/1.02      ( ~ r1_tarski(sK3,u1_struct_0(sK0))
% 3.98/1.02      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(instantiation,[status(thm)],[c_1529]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_2880,plain,
% 3.98/1.02      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 3.98/1.02      inference(global_propositional_subsumption,
% 3.98/1.02                [status(thm)],
% 3.98/1.02                [c_1327,c_21,c_20,c_600,c_1411,c_1492,c_1836,c_2081]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1336,plain,
% 3.98/1.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.98/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_26,plain,
% 3.98/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_27,plain,
% 3.98/1.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.98/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1412,plain,
% 3.98/1.02      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
% 3.98/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_1411]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1493,plain,
% 3.98/1.02      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.98/1.02      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 3.98/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_1492]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1557,plain,
% 3.98/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.98/1.02      inference(global_propositional_subsumption,
% 3.98/1.02                [status(thm)],
% 3.98/1.02                [c_1336,c_26,c_27,c_1412,c_1493]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_9,plain,
% 3.98/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.98/1.02      | ~ l1_pre_topc(X1)
% 3.98/1.02      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.98/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_453,plain,
% 3.98/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.98/1.02      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 3.98/1.02      | sK0 != X1 ),
% 3.98/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_454,plain,
% 3.98/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.98/1.02      inference(unflattening,[status(thm)],[c_453]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1330,plain,
% 3.98/1.02      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.98/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_2365,plain,
% 3.98/1.02      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_1557,c_1330]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_2882,plain,
% 3.98/1.02      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
% 3.98/1.02      inference(demodulation,[status(thm)],[c_2880,c_2365]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1341,plain,
% 3.98/1.02      ( r1_tarski(X0,X1) = iProver_top
% 3.98/1.02      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1869,plain,
% 3.98/1.02      ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_1557,c_1341]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1,plain,
% 3.98/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.98/1.02      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.98/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_239,plain,
% 3.98/1.02      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.98/1.02      inference(bin_hyper_res,[status(thm)],[c_1,c_188]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1333,plain,
% 3.98/1.02      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.98/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_2654,plain,
% 3.98/1.02      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_1869,c_1333]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_2883,plain,
% 3.98/1.02      ( k1_tops_1(sK0,sK3) = sK3 ),
% 3.98/1.02      inference(light_normalisation,[status(thm)],[c_2882,c_2654]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_15,plain,
% 3.98/1.02      ( ~ r1_tarski(X0,X1)
% 3.98/1.02      | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.98/1.02      | ~ l1_pre_topc(X2) ),
% 3.98/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_480,plain,
% 3.98/1.02      ( ~ r1_tarski(X0,X1)
% 3.98/1.02      | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.98/1.02      | sK0 != X2 ),
% 3.98/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_481,plain,
% 3.98/1.02      ( ~ r1_tarski(X0,X1)
% 3.98/1.02      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
% 3.98/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.98/1.02      inference(unflattening,[status(thm)],[c_480]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1329,plain,
% 3.98/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.98/1.02      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top
% 3.98/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.98/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_6478,plain,
% 3.98/1.02      ( r1_tarski(sK3,X0) != iProver_top
% 3.98/1.02      | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top
% 3.98/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.98/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_2883,c_1329]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_7517,plain,
% 3.98/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.98/1.02      | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top
% 3.98/1.02      | r1_tarski(sK3,X0) != iProver_top ),
% 3.98/1.02      inference(global_propositional_subsumption,
% 3.98/1.02                [status(thm)],
% 3.98/1.02                [c_6478,c_26,c_27,c_1412,c_1493]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_7518,plain,
% 3.98/1.02      ( r1_tarski(sK3,X0) != iProver_top
% 3.98/1.02      | r1_tarski(sK3,k1_tops_1(sK0,X0)) = iProver_top
% 3.98/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.98/1.02      inference(renaming,[status(thm)],[c_7517]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_7526,plain,
% 3.98/1.02      ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top
% 3.98/1.02      | r1_tarski(sK3,sK2) != iProver_top ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_1335,c_7518]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_18,negated_conjecture,
% 3.98/1.02      ( r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 3.98/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_29,plain,
% 3.98/1.02      ( r1_tarski(sK3,sK2) = iProver_top
% 3.98/1.02      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_7743,plain,
% 3.98/1.02      ( r1_tarski(sK3,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.98/1.02      inference(global_propositional_subsumption,
% 3.98/1.02                [status(thm)],
% 3.98/1.02                [c_7526,c_26,c_29,c_1412,c_1493]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1342,plain,
% 3.98/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.98/1.02      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_5,plain,
% 3.98/1.02      ( ~ r2_hidden(X0,X1)
% 3.98/1.02      | m1_subset_1(X0,X2)
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.98/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1340,plain,
% 3.98/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.98/1.02      | m1_subset_1(X0,X2) = iProver_top
% 3.98/1.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_2579,plain,
% 3.98/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.98/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.98/1.02      | m1_subset_1(X2,X1) = iProver_top ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_1342,c_1340]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_7747,plain,
% 3.98/1.02      ( r2_hidden(X0,sK3) != iProver_top
% 3.98/1.02      | m1_subset_1(X0,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_7743,c_2579]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_2,plain,
% 3.98/1.02      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.98/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1343,plain,
% 3.98/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.98/1.02      | m1_subset_1(X0,X1) != iProver_top
% 3.98/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_8240,plain,
% 3.98/1.02      ( r2_hidden(X0,k1_tops_1(sK0,sK2)) = iProver_top
% 3.98/1.02      | r2_hidden(X0,sK3) != iProver_top
% 3.98/1.02      | v1_xboole_0(k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_7747,c_1343]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_6,plain,
% 3.98/1.02      ( ~ r2_hidden(X0,X1)
% 3.98/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.98/1.02      | ~ v1_xboole_0(X2) ),
% 3.98/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1339,plain,
% 3.98/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.98/1.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.98/1.02      | v1_xboole_0(X2) != iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_2114,plain,
% 3.98/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.98/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.98/1.02      | v1_xboole_0(X1) != iProver_top ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_1342,c_1339]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_7748,plain,
% 3.98/1.02      ( r2_hidden(X0,sK3) != iProver_top
% 3.98/1.02      | v1_xboole_0(k1_tops_1(sK0,sK2)) != iProver_top ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_7743,c_2114]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_9379,plain,
% 3.98/1.02      ( r2_hidden(X0,sK3) != iProver_top
% 3.98/1.02      | r2_hidden(X0,k1_tops_1(sK0,sK2)) = iProver_top ),
% 3.98/1.02      inference(global_propositional_subsumption,
% 3.98/1.02                [status(thm)],
% 3.98/1.02                [c_8240,c_7748]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_9380,plain,
% 3.98/1.02      ( r2_hidden(X0,k1_tops_1(sK0,sK2)) = iProver_top
% 3.98/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 3.98/1.02      inference(renaming,[status(thm)],[c_9379]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1325,plain,
% 3.98/1.02      ( r1_tarski(k1_tops_1(sK0,X0),sK2) != iProver_top
% 3.98/1.02      | r2_hidden(sK1,k1_tops_1(sK0,X0)) != iProver_top
% 3.98/1.02      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 3.98/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_1862,plain,
% 3.98/1.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top ),
% 3.98/1.02      inference(global_propositional_subsumption,
% 3.98/1.02                [status(thm)],
% 3.98/1.02                [c_1325,c_26,c_1412,c_1493]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_9385,plain,
% 3.98/1.02      ( r2_hidden(sK1,sK3) != iProver_top ),
% 3.98/1.02      inference(superposition,[status(thm)],[c_9380,c_1862]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_17,negated_conjecture,
% 3.98/1.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r2_hidden(sK1,sK3) ),
% 3.98/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(c_30,plain,
% 3.98/1.02      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.98/1.02      | r2_hidden(sK1,sK3) = iProver_top ),
% 3.98/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.98/1.02  
% 3.98/1.02  cnf(contradiction,plain,
% 3.98/1.02      ( $false ),
% 3.98/1.02      inference(minisat,[status(thm)],[c_9385,c_1493,c_1412,c_30,c_26]) ).
% 3.98/1.02  
% 3.98/1.02  
% 3.98/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.98/1.02  
% 3.98/1.02  ------                               Statistics
% 3.98/1.02  
% 3.98/1.02  ------ General
% 3.98/1.02  
% 3.98/1.02  abstr_ref_over_cycles:                  0
% 3.98/1.02  abstr_ref_under_cycles:                 0
% 3.98/1.02  gc_basic_clause_elim:                   0
% 3.98/1.02  forced_gc_time:                         0
% 3.98/1.02  parsing_time:                           0.01
% 3.98/1.02  unif_index_cands_time:                  0.
% 3.98/1.02  unif_index_add_time:                    0.
% 3.98/1.02  orderings_time:                         0.
% 3.98/1.02  out_proof_time:                         0.011
% 3.98/1.02  total_time:                             0.31
% 3.98/1.02  num_of_symbols:                         48
% 3.98/1.02  num_of_terms:                           9798
% 3.98/1.02  
% 3.98/1.02  ------ Preprocessing
% 3.98/1.02  
% 3.98/1.02  num_of_splits:                          0
% 3.98/1.02  num_of_split_atoms:                     0
% 3.98/1.02  num_of_reused_defs:                     0
% 3.98/1.02  num_eq_ax_congr_red:                    5
% 3.98/1.02  num_of_sem_filtered_clauses:            1
% 3.98/1.02  num_of_subtypes:                        0
% 3.98/1.02  monotx_restored_types:                  0
% 3.98/1.02  sat_num_of_epr_types:                   0
% 3.98/1.02  sat_num_of_non_cyclic_types:            0
% 3.98/1.02  sat_guarded_non_collapsed_types:        0
% 3.98/1.02  num_pure_diseq_elim:                    0
% 3.98/1.02  simp_replaced_by:                       0
% 3.98/1.02  res_preprocessed:                       102
% 3.98/1.02  prep_upred:                             0
% 3.98/1.02  prep_unflattend:                        17
% 3.98/1.02  smt_new_axioms:                         0
% 3.98/1.02  pred_elim_cands:                        4
% 3.98/1.02  pred_elim:                              4
% 3.98/1.02  pred_elim_cl:                           5
% 3.98/1.02  pred_elim_cycles:                       7
% 3.98/1.02  merged_defs:                            8
% 3.98/1.02  merged_defs_ncl:                        0
% 3.98/1.02  bin_hyper_res:                          10
% 3.98/1.02  prep_cycles:                            4
% 3.98/1.02  pred_elim_time:                         0.008
% 3.98/1.02  splitting_time:                         0.
% 3.98/1.02  sem_filter_time:                        0.
% 3.98/1.02  monotx_time:                            0.001
% 3.98/1.02  subtype_inf_time:                       0.
% 3.98/1.02  
% 3.98/1.02  ------ Problem properties
% 3.98/1.02  
% 3.98/1.02  clauses:                                19
% 3.98/1.02  conjectures:                            4
% 3.98/1.02  epr:                                    1
% 3.98/1.02  horn:                                   14
% 3.98/1.02  ground:                                 5
% 3.98/1.02  unary:                                  1
% 3.98/1.02  binary:                                 10
% 3.98/1.02  lits:                                   50
% 3.98/1.02  lits_eq:                                5
% 3.98/1.02  fd_pure:                                0
% 3.98/1.02  fd_pseudo:                              0
% 3.98/1.02  fd_cond:                                0
% 3.98/1.02  fd_pseudo_cond:                         0
% 3.98/1.02  ac_symbols:                             0
% 3.98/1.02  
% 3.98/1.02  ------ Propositional Solver
% 3.98/1.02  
% 3.98/1.02  prop_solver_calls:                      29
% 3.98/1.02  prop_fast_solver_calls:                 918
% 3.98/1.02  smt_solver_calls:                       0
% 3.98/1.02  smt_fast_solver_calls:                  0
% 3.98/1.02  prop_num_of_clauses:                    4701
% 3.98/1.02  prop_preprocess_simplified:             10061
% 3.98/1.02  prop_fo_subsumed:                       34
% 3.98/1.02  prop_solver_time:                       0.
% 3.98/1.02  smt_solver_time:                        0.
% 3.98/1.02  smt_fast_solver_time:                   0.
% 3.98/1.02  prop_fast_solver_time:                  0.
% 3.98/1.02  prop_unsat_core_time:                   0.
% 3.98/1.02  
% 3.98/1.02  ------ QBF
% 3.98/1.02  
% 3.98/1.02  qbf_q_res:                              0
% 3.98/1.02  qbf_num_tautologies:                    0
% 3.98/1.02  qbf_prep_cycles:                        0
% 3.98/1.02  
% 3.98/1.02  ------ BMC1
% 3.98/1.02  
% 3.98/1.02  bmc1_current_bound:                     -1
% 3.98/1.02  bmc1_last_solved_bound:                 -1
% 3.98/1.02  bmc1_unsat_core_size:                   -1
% 3.98/1.02  bmc1_unsat_core_parents_size:           -1
% 3.98/1.02  bmc1_merge_next_fun:                    0
% 3.98/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.98/1.02  
% 3.98/1.02  ------ Instantiation
% 3.98/1.02  
% 3.98/1.02  inst_num_of_clauses:                    1474
% 3.98/1.02  inst_num_in_passive:                    463
% 3.98/1.02  inst_num_in_active:                     529
% 3.98/1.02  inst_num_in_unprocessed:                482
% 3.98/1.02  inst_num_of_loops:                      550
% 3.98/1.02  inst_num_of_learning_restarts:          0
% 3.98/1.02  inst_num_moves_active_passive:          20
% 3.98/1.02  inst_lit_activity:                      0
% 3.98/1.02  inst_lit_activity_moves:                0
% 3.98/1.02  inst_num_tautologies:                   0
% 3.98/1.02  inst_num_prop_implied:                  0
% 3.98/1.02  inst_num_existing_simplified:           0
% 3.98/1.02  inst_num_eq_res_simplified:             0
% 3.98/1.02  inst_num_child_elim:                    0
% 3.98/1.02  inst_num_of_dismatching_blockings:      383
% 3.98/1.02  inst_num_of_non_proper_insts:           1517
% 3.98/1.02  inst_num_of_duplicates:                 0
% 3.98/1.02  inst_inst_num_from_inst_to_res:         0
% 3.98/1.02  inst_dismatching_checking_time:         0.
% 3.98/1.02  
% 3.98/1.02  ------ Resolution
% 3.98/1.02  
% 3.98/1.02  res_num_of_clauses:                     0
% 3.98/1.02  res_num_in_passive:                     0
% 3.98/1.02  res_num_in_active:                      0
% 3.98/1.02  res_num_of_loops:                       106
% 3.98/1.02  res_forward_subset_subsumed:            59
% 3.98/1.02  res_backward_subset_subsumed:           0
% 3.98/1.02  res_forward_subsumed:                   0
% 3.98/1.02  res_backward_subsumed:                  0
% 3.98/1.02  res_forward_subsumption_resolution:     0
% 3.98/1.02  res_backward_subsumption_resolution:    0
% 3.98/1.02  res_clause_to_clause_subsumption:       665
% 3.98/1.02  res_orphan_elimination:                 0
% 3.98/1.02  res_tautology_del:                      86
% 3.98/1.02  res_num_eq_res_simplified:              0
% 3.98/1.02  res_num_sel_changes:                    0
% 3.98/1.02  res_moves_from_active_to_pass:          0
% 3.98/1.02  
% 3.98/1.02  ------ Superposition
% 3.98/1.02  
% 3.98/1.02  sup_time_total:                         0.
% 3.98/1.02  sup_time_generating:                    0.
% 3.98/1.02  sup_time_sim_full:                      0.
% 3.98/1.02  sup_time_sim_immed:                     0.
% 3.98/1.02  
% 3.98/1.02  sup_num_of_clauses:                     192
% 3.98/1.02  sup_num_in_active:                      99
% 3.98/1.02  sup_num_in_passive:                     93
% 3.98/1.02  sup_num_of_loops:                       108
% 3.98/1.02  sup_fw_superposition:                   220
% 3.98/1.03  sup_bw_superposition:                   83
% 3.98/1.03  sup_immediate_simplified:               64
% 3.98/1.03  sup_given_eliminated:                   0
% 3.98/1.03  comparisons_done:                       0
% 3.98/1.03  comparisons_avoided:                    0
% 3.98/1.03  
% 3.98/1.03  ------ Simplifications
% 3.98/1.03  
% 3.98/1.03  
% 3.98/1.03  sim_fw_subset_subsumed:                 33
% 3.98/1.03  sim_bw_subset_subsumed:                 3
% 3.98/1.03  sim_fw_subsumed:                        3
% 3.98/1.03  sim_bw_subsumed:                        6
% 3.98/1.03  sim_fw_subsumption_res:                 0
% 3.98/1.03  sim_bw_subsumption_res:                 0
% 3.98/1.03  sim_tautology_del:                      8
% 3.98/1.03  sim_eq_tautology_del:                   15
% 3.98/1.03  sim_eq_res_simp:                        0
% 3.98/1.03  sim_fw_demodulated:                     0
% 3.98/1.03  sim_bw_demodulated:                     2
% 3.98/1.03  sim_light_normalised:                   34
% 3.98/1.03  sim_joinable_taut:                      0
% 3.98/1.03  sim_joinable_simp:                      0
% 3.98/1.03  sim_ac_normalised:                      0
% 3.98/1.03  sim_smt_subsumption:                    0
% 3.98/1.03  
%------------------------------------------------------------------------------
