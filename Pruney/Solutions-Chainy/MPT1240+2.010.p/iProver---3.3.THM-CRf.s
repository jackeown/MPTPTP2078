%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:59 EST 2020

% Result     : Theorem 11.81s
% Output     : CNFRefutation 11.81s
% Verified   : 
% Statistics : Number of formulae       :  152 (1505 expanded)
%              Number of clauses        :   90 ( 387 expanded)
%              Number of leaves         :   16 ( 362 expanded)
%              Depth                    :   25
%              Number of atoms          :  540 (12125 expanded)
%              Number of equality atoms :  135 ( 400 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK4)
        & r1_tarski(sK4,X2)
        & v3_pre_topc(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
              ( ~ r2_hidden(sK2,X3)
              | ~ r1_tarski(X3,sK3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK2,k1_tops_1(X0,sK3)) )
        & ( ? [X4] :
              ( r2_hidden(sK2,X4)
              & r1_tarski(X4,sK3)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK2,k1_tops_1(X0,sK3)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
                | ~ v3_pre_topc(X3,sK1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            | ~ r2_hidden(X1,k1_tops_1(sK1,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK1)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
            | r2_hidden(X1,k1_tops_1(sK1,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK2,X3)
          | ~ r1_tarski(X3,sK3)
          | ~ v3_pre_topc(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) )
    & ( ( r2_hidden(sK2,sK4)
        & r1_tarski(sK4,sK3)
        & v3_pre_topc(sK4,sK1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) )
      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f41,f40,f39])).

fof(f62,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r1_tarski(X3,sK3)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,
    ( v3_pre_topc(sK4,sK1)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,
    ( r1_tarski(sK4,sK3)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_879,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_864,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1133,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1134,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1139,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1140,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_11,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1177,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1178,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1177])).

cnf(c_16,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1275,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK1,sK3),sK1)
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1276,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1275])).

cnf(c_1285,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_864,c_24,c_25,c_26,c_27,c_1134,c_1140,c_1178,c_1276])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_878,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1368,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_878])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_164,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_165,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_165])).

cnf(c_859,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_1639,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_1368,c_859])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_872,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) != iProver_top
    | v4_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3672,plain,
    ( v3_pre_topc(sK4,sK1) != iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_872])).

cnf(c_19,negated_conjecture,
    ( v3_pre_topc(sK4,sK1)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,plain,
    ( v3_pre_topc(sK4,sK1) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6357,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3672,c_24,c_25,c_26,c_28,c_1134,c_1140,c_1178,c_1276])).

cnf(c_6358,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6357])).

cnf(c_6364,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK1),sK4),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_6358])).

cnf(c_1227,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r1_tarski(sK4,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

cnf(c_1228,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_211,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_165])).

cnf(c_860,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_6363,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top
    | r1_tarski(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_860,c_6358])).

cnf(c_6845,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6364,c_24,c_25,c_26,c_1134,c_1140,c_1178,c_1228,c_1276,c_6363])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_876,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2378,plain,
    ( k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) = k3_subset_1(u1_struct_0(X0),X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_860,c_876])).

cnf(c_7606,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK4)) = k3_subset_1(u1_struct_0(sK1),sK4)
    | r1_tarski(sK4,u1_struct_0(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6845,c_2378])).

cnf(c_40117,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK4)) = k3_subset_1(u1_struct_0(sK1),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7606,c_24,c_25,c_26,c_1134,c_1140,c_1178,c_1228,c_1276])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_875,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3423,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_875])).

cnf(c_1347,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3777,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3423,c_23,c_22,c_21,c_20,c_1133,c_1139,c_1177,c_1275,c_1347])).

cnf(c_40122,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK4)) = k1_tops_1(sK1,sK4) ),
    inference(demodulation,[status(thm)],[c_40117,c_3777])).

cnf(c_40124,plain,
    ( k1_tops_1(sK1,sK4) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_40122,c_1639])).

cnf(c_863,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_869,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3236,plain,
    ( k3_subset_1(k1_tops_1(X0,X1),k3_subset_1(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) = k1_tops_1(X0,X2)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_859])).

cnf(c_10272,plain,
    ( k3_subset_1(k1_tops_1(sK1,sK3),k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_863,c_3236])).

cnf(c_11255,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k3_subset_1(k1_tops_1(sK1,sK3),k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10272,c_25])).

cnf(c_11256,plain,
    ( k3_subset_1(k1_tops_1(sK1,sK3),k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_11255])).

cnf(c_11267,plain,
    ( k3_subset_1(k1_tops_1(sK1,sK3),k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4))) = k1_tops_1(sK1,sK4)
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_11256])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11316,plain,
    ( k3_subset_1(k1_tops_1(sK1,sK3),k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4))) = k1_tops_1(sK1,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11267,c_24,c_25,c_26,c_29,c_1134,c_1140,c_1178,c_1276])).

cnf(c_11319,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
    | r1_tarski(k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)),k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11316,c_860])).

cnf(c_1251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK3)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1400,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3))
    | ~ r1_tarski(sK4,sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_1401,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(sK4,sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_4363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK1,sK3)))
    | ~ r1_tarski(X0,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_10872,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_4363])).

cnf(c_10873,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10872])).

cnf(c_12691,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11319,c_24,c_25,c_26,c_27,c_29,c_1134,c_1140,c_1178,c_1276,c_1401,c_10873])).

cnf(c_41104,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_40124,c_12691])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3965,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_tops_1(sK1,sK3)))
    | r1_tarski(sK4,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_3966,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
    | r1_tarski(sK4,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3965])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1330,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3215,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r2_hidden(sK2,sK4)
    | ~ r1_tarski(sK4,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_3216,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r1_tarski(sK4,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3215])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41104,c_3966,c_3216,c_1276,c_1178,c_1140,c_1134,c_30,c_26,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:49:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.81/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.81/1.99  
% 11.81/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.81/1.99  
% 11.81/1.99  ------  iProver source info
% 11.81/1.99  
% 11.81/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.81/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.81/1.99  git: non_committed_changes: false
% 11.81/1.99  git: last_make_outside_of_git: false
% 11.81/1.99  
% 11.81/1.99  ------ 
% 11.81/1.99  ------ Parsing...
% 11.81/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.81/1.99  
% 11.81/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.81/1.99  
% 11.81/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.81/1.99  
% 11.81/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.81/1.99  ------ Proving...
% 11.81/1.99  ------ Problem Properties 
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  clauses                                 24
% 11.81/1.99  conjectures                             8
% 11.81/1.99  EPR                                     3
% 11.81/1.99  Horn                                    19
% 11.81/1.99  unary                                   3
% 11.81/1.99  binary                                  10
% 11.81/1.99  lits                                    66
% 11.81/1.99  lits eq                                 4
% 11.81/1.99  fd_pure                                 0
% 11.81/1.99  fd_pseudo                               0
% 11.81/1.99  fd_cond                                 0
% 11.81/1.99  fd_pseudo_cond                          0
% 11.81/1.99  AC symbols                              0
% 11.81/1.99  
% 11.81/1.99  ------ Input Options Time Limit: Unbounded
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  ------ 
% 11.81/1.99  Current options:
% 11.81/1.99  ------ 
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  ------ Proving...
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  % SZS status Theorem for theBenchmark.p
% 11.81/1.99  
% 11.81/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.81/1.99  
% 11.81/1.99  fof(f4,axiom,(
% 11.81/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f34,plain,(
% 11.81/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.81/1.99    inference(nnf_transformation,[],[f4])).
% 11.81/1.99  
% 11.81/1.99  fof(f49,plain,(
% 11.81/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f34])).
% 11.81/1.99  
% 11.81/1.99  fof(f12,conjecture,(
% 11.81/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f13,negated_conjecture,(
% 11.81/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 11.81/1.99    inference(negated_conjecture,[],[f12])).
% 11.81/1.99  
% 11.81/1.99  fof(f28,plain,(
% 11.81/1.99    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f13])).
% 11.81/1.99  
% 11.81/1.99  fof(f29,plain,(
% 11.81/1.99    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.81/1.99    inference(flattening,[],[f28])).
% 11.81/1.99  
% 11.81/1.99  fof(f36,plain,(
% 11.81/1.99    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.81/1.99    inference(nnf_transformation,[],[f29])).
% 11.81/1.99  
% 11.81/1.99  fof(f37,plain,(
% 11.81/1.99    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.81/1.99    inference(flattening,[],[f36])).
% 11.81/1.99  
% 11.81/1.99  fof(f38,plain,(
% 11.81/1.99    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.81/1.99    inference(rectify,[],[f37])).
% 11.81/1.99  
% 11.81/1.99  fof(f41,plain,(
% 11.81/1.99    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK4) & r1_tarski(sK4,X2) & v3_pre_topc(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f40,plain,(
% 11.81/1.99    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK2,k1_tops_1(X0,sK3))) & (? [X4] : (r2_hidden(sK2,X4) & r1_tarski(X4,sK3) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK2,k1_tops_1(X0,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f39,plain,(
% 11.81/1.99    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X1,k1_tops_1(sK1,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(X1,k1_tops_1(sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f42,plain,(
% 11.81/1.99    ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(sK2,k1_tops_1(sK1,sK3))) & ((r2_hidden(sK2,sK4) & r1_tarski(sK4,sK3) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(sK2,k1_tops_1(sK1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f41,f40,f39])).
% 11.81/1.99  
% 11.81/1.99  fof(f62,plain,(
% 11.81/1.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.81/1.99    inference(cnf_transformation,[],[f42])).
% 11.81/1.99  
% 11.81/1.99  fof(f59,plain,(
% 11.81/1.99    v2_pre_topc(sK1)),
% 11.81/1.99    inference(cnf_transformation,[],[f42])).
% 11.81/1.99  
% 11.81/1.99  fof(f60,plain,(
% 11.81/1.99    l1_pre_topc(sK1)),
% 11.81/1.99    inference(cnf_transformation,[],[f42])).
% 11.81/1.99  
% 11.81/1.99  fof(f61,plain,(
% 11.81/1.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 11.81/1.99    inference(cnf_transformation,[],[f42])).
% 11.81/1.99  
% 11.81/1.99  fof(f7,axiom,(
% 11.81/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f20,plain,(
% 11.81/1.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f7])).
% 11.81/1.99  
% 11.81/1.99  fof(f21,plain,(
% 11.81/1.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.81/1.99    inference(flattening,[],[f20])).
% 11.81/1.99  
% 11.81/1.99  fof(f53,plain,(
% 11.81/1.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f21])).
% 11.81/1.99  
% 11.81/1.99  fof(f10,axiom,(
% 11.81/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f25,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/1.99    inference(ennf_transformation,[],[f10])).
% 11.81/1.99  
% 11.81/1.99  fof(f57,plain,(
% 11.81/1.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f25])).
% 11.81/1.99  
% 11.81/1.99  fof(f8,axiom,(
% 11.81/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f22,plain,(
% 11.81/1.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f8])).
% 11.81/1.99  
% 11.81/1.99  fof(f23,plain,(
% 11.81/1.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.81/1.99    inference(flattening,[],[f22])).
% 11.81/1.99  
% 11.81/1.99  fof(f54,plain,(
% 11.81/1.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f23])).
% 11.81/1.99  
% 11.81/1.99  fof(f66,plain,(
% 11.81/1.99    ( ! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK2,k1_tops_1(sK1,sK3))) )),
% 11.81/1.99    inference(cnf_transformation,[],[f42])).
% 11.81/1.99  
% 11.81/1.99  fof(f48,plain,(
% 11.81/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.81/1.99    inference(cnf_transformation,[],[f34])).
% 11.81/1.99  
% 11.81/1.99  fof(f3,axiom,(
% 11.81/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f16,plain,(
% 11.81/1.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f3])).
% 11.81/1.99  
% 11.81/1.99  fof(f47,plain,(
% 11.81/1.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.81/1.99    inference(cnf_transformation,[],[f16])).
% 11.81/1.99  
% 11.81/1.99  fof(f9,axiom,(
% 11.81/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f24,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/1.99    inference(ennf_transformation,[],[f9])).
% 11.81/1.99  
% 11.81/1.99  fof(f35,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/1.99    inference(nnf_transformation,[],[f24])).
% 11.81/1.99  
% 11.81/1.99  fof(f56,plain,(
% 11.81/1.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f35])).
% 11.81/1.99  
% 11.81/1.99  fof(f63,plain,(
% 11.81/1.99    v3_pre_topc(sK4,sK1) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.81/1.99    inference(cnf_transformation,[],[f42])).
% 11.81/1.99  
% 11.81/1.99  fof(f2,axiom,(
% 11.81/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f15,plain,(
% 11.81/1.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f2])).
% 11.81/1.99  
% 11.81/1.99  fof(f46,plain,(
% 11.81/1.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.81/1.99    inference(cnf_transformation,[],[f15])).
% 11.81/1.99  
% 11.81/1.99  fof(f5,axiom,(
% 11.81/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f17,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/1.99    inference(ennf_transformation,[],[f5])).
% 11.81/1.99  
% 11.81/1.99  fof(f18,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/1.99    inference(flattening,[],[f17])).
% 11.81/1.99  
% 11.81/1.99  fof(f50,plain,(
% 11.81/1.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f18])).
% 11.81/1.99  
% 11.81/1.99  fof(f6,axiom,(
% 11.81/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f19,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/1.99    inference(ennf_transformation,[],[f6])).
% 11.81/1.99  
% 11.81/1.99  fof(f52,plain,(
% 11.81/1.99    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f19])).
% 11.81/1.99  
% 11.81/1.99  fof(f11,axiom,(
% 11.81/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f26,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/1.99    inference(ennf_transformation,[],[f11])).
% 11.81/1.99  
% 11.81/1.99  fof(f27,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/1.99    inference(flattening,[],[f26])).
% 11.81/1.99  
% 11.81/1.99  fof(f58,plain,(
% 11.81/1.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f27])).
% 11.81/1.99  
% 11.81/1.99  fof(f64,plain,(
% 11.81/1.99    r1_tarski(sK4,sK3) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.81/1.99    inference(cnf_transformation,[],[f42])).
% 11.81/1.99  
% 11.81/1.99  fof(f1,axiom,(
% 11.81/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f14,plain,(
% 11.81/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f1])).
% 11.81/1.99  
% 11.81/1.99  fof(f30,plain,(
% 11.81/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.81/1.99    inference(nnf_transformation,[],[f14])).
% 11.81/1.99  
% 11.81/1.99  fof(f31,plain,(
% 11.81/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.81/1.99    inference(rectify,[],[f30])).
% 11.81/1.99  
% 11.81/1.99  fof(f32,plain,(
% 11.81/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f33,plain,(
% 11.81/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 11.81/1.99  
% 11.81/1.99  fof(f43,plain,(
% 11.81/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f33])).
% 11.81/1.99  
% 11.81/1.99  fof(f65,plain,(
% 11.81/1.99    r2_hidden(sK2,sK4) | r2_hidden(sK2,k1_tops_1(sK1,sK3))),
% 11.81/1.99    inference(cnf_transformation,[],[f42])).
% 11.81/1.99  
% 11.81/1.99  cnf(c_5,plain,
% 11.81/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.81/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_879,plain,
% 11.81/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.81/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_20,negated_conjecture,
% 11.81/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 11.81/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_864,plain,
% 11.81/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 11.81/1.99      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_23,negated_conjecture,
% 11.81/1.99      ( v2_pre_topc(sK1) ),
% 11.81/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_24,plain,
% 11.81/1.99      ( v2_pre_topc(sK1) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_22,negated_conjecture,
% 11.81/1.99      ( l1_pre_topc(sK1) ),
% 11.81/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_25,plain,
% 11.81/1.99      ( l1_pre_topc(sK1) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_21,negated_conjecture,
% 11.81/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.81/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_26,plain,
% 11.81/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_27,plain,
% 11.81/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 11.81/1.99      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_10,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/1.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/1.99      | ~ l1_pre_topc(X1) ),
% 11.81/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1133,plain,
% 11.81/1.99      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | ~ l1_pre_topc(sK1) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1134,plain,
% 11.81/1.99      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 11.81/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | l1_pre_topc(sK1) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_14,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/1.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.81/1.99      | ~ l1_pre_topc(X1) ),
% 11.81/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1139,plain,
% 11.81/1.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | r1_tarski(k1_tops_1(sK1,sK3),sK3)
% 11.81/1.99      | ~ l1_pre_topc(sK1) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_14]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1140,plain,
% 11.81/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top
% 11.81/1.99      | l1_pre_topc(sK1) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_1139]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_11,plain,
% 11.81/1.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.81/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.81/1.99      | ~ l1_pre_topc(X0)
% 11.81/1.99      | ~ v2_pre_topc(X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1177,plain,
% 11.81/1.99      ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1)
% 11.81/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | ~ l1_pre_topc(sK1)
% 11.81/1.99      | ~ v2_pre_topc(sK1) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1178,plain,
% 11.81/1.99      ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1) = iProver_top
% 11.81/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.81/1.99      | v2_pre_topc(sK1) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_1177]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_16,negated_conjecture,
% 11.81/1.99      ( ~ v3_pre_topc(X0,sK1)
% 11.81/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | ~ r2_hidden(sK2,X0)
% 11.81/1.99      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.81/1.99      | ~ r1_tarski(X0,sK3) ),
% 11.81/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1275,plain,
% 11.81/1.99      ( ~ v3_pre_topc(k1_tops_1(sK1,sK3),sK1)
% 11.81/1.99      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.81/1.99      | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_16]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1276,plain,
% 11.81/1.99      ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 11.81/1.99      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
% 11.81/1.99      | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_1275]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1285,plain,
% 11.81/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_864,c_24,c_25,c_26,c_27,c_1134,c_1140,c_1178,c_1276]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_6,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.81/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_878,plain,
% 11.81/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.81/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1368,plain,
% 11.81/1.99      ( r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_1285,c_878]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_4,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.81/1.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 11.81/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_164,plain,
% 11.81/1.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.81/1.99      inference(prop_impl,[status(thm)],[c_5]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_165,plain,
% 11.81/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_164]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_212,plain,
% 11.81/1.99      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 11.81/1.99      inference(bin_hyper_res,[status(thm)],[c_4,c_165]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_859,plain,
% 11.81/1.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 11.81/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1639,plain,
% 11.81/1.99      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK4)) = sK4 ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_1368,c_859]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_12,plain,
% 11.81/1.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 11.81/1.99      | v4_pre_topc(X1,X0)
% 11.81/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.81/1.99      | ~ l1_pre_topc(X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_872,plain,
% 11.81/1.99      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) != iProver_top
% 11.81/1.99      | v4_pre_topc(X1,X0) = iProver_top
% 11.81/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.81/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3672,plain,
% 11.81/1.99      ( v3_pre_topc(sK4,sK1) != iProver_top
% 11.81/1.99      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top
% 11.81/1.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | l1_pre_topc(sK1) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_1639,c_872]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_19,negated_conjecture,
% 11.81/1.99      ( v3_pre_topc(sK4,sK1) | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 11.81/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_28,plain,
% 11.81/1.99      ( v3_pre_topc(sK4,sK1) = iProver_top
% 11.81/1.99      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_6357,plain,
% 11.81/1.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_3672,c_24,c_25,c_26,c_28,c_1134,c_1140,c_1178,c_1276]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_6358,plain,
% 11.81/1.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top
% 11.81/1.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_6357]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_6364,plain,
% 11.81/1.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top
% 11.81/1.99      | r1_tarski(k3_subset_1(u1_struct_0(sK1),sK4),u1_struct_0(sK1)) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_879,c_6358]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1227,plain,
% 11.81/1.99      ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.81/1.99      | r1_tarski(sK4,u1_struct_0(sK1)) ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_6,c_20]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1228,plain,
% 11.81/1.99      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 11.81/1.99      | r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.81/1.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 11.81/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_211,plain,
% 11.81/1.99      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 11.81/1.99      | ~ r1_tarski(X1,X0) ),
% 11.81/1.99      inference(bin_hyper_res,[status(thm)],[c_3,c_165]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_860,plain,
% 11.81/1.99      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 11.81/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_6363,plain,
% 11.81/1.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top
% 11.81/1.99      | r1_tarski(sK4,u1_struct_0(sK1)) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_860,c_6358]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_6845,plain,
% 11.81/1.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK4),sK1) = iProver_top ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_6364,c_24,c_25,c_26,c_1134,c_1140,c_1178,c_1228,
% 11.81/1.99                 c_1276,c_6363]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_8,plain,
% 11.81/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/1.99      | ~ l1_pre_topc(X1)
% 11.81/1.99      | k2_pre_topc(X1,X0) = X0 ),
% 11.81/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_876,plain,
% 11.81/1.99      ( k2_pre_topc(X0,X1) = X1
% 11.81/1.99      | v4_pre_topc(X1,X0) != iProver_top
% 11.81/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.81/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_2378,plain,
% 11.81/1.99      ( k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) = k3_subset_1(u1_struct_0(X0),X1)
% 11.81/1.99      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) != iProver_top
% 11.81/1.99      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 11.81/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_860,c_876]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_7606,plain,
% 11.81/1.99      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK4)) = k3_subset_1(u1_struct_0(sK1),sK4)
% 11.81/1.99      | r1_tarski(sK4,u1_struct_0(sK1)) != iProver_top
% 11.81/1.99      | l1_pre_topc(sK1) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_6845,c_2378]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_40117,plain,
% 11.81/1.99      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK4)) = k3_subset_1(u1_struct_0(sK1),sK4) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_7606,c_24,c_25,c_26,c_1134,c_1140,c_1178,c_1228,
% 11.81/1.99                 c_1276]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_9,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/1.99      | ~ l1_pre_topc(X1)
% 11.81/1.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_875,plain,
% 11.81/1.99      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 11.81/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.81/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3423,plain,
% 11.81/1.99      ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4)
% 11.81/1.99      | l1_pre_topc(sK1) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_1285,c_875]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1347,plain,
% 11.81/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | ~ l1_pre_topc(sK1)
% 11.81/1.99      | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3777,plain,
% 11.81/1.99      ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK4))) = k1_tops_1(sK1,sK4) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_3423,c_23,c_22,c_21,c_20,c_1133,c_1139,c_1177,c_1275,
% 11.81/1.99                 c_1347]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_40122,plain,
% 11.81/1.99      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK4)) = k1_tops_1(sK1,sK4) ),
% 11.81/1.99      inference(demodulation,[status(thm)],[c_40117,c_3777]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_40124,plain,
% 11.81/1.99      ( k1_tops_1(sK1,sK4) = sK4 ),
% 11.81/1.99      inference(light_normalisation,[status(thm)],[c_40122,c_1639]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_863,plain,
% 11.81/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_15,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/1.99      | ~ r1_tarski(X0,X2)
% 11.81/1.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.81/1.99      | ~ l1_pre_topc(X1) ),
% 11.81/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_869,plain,
% 11.81/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.81/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.81/1.99      | r1_tarski(X0,X2) != iProver_top
% 11.81/1.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
% 11.81/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3236,plain,
% 11.81/1.99      ( k3_subset_1(k1_tops_1(X0,X1),k3_subset_1(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) = k1_tops_1(X0,X2)
% 11.81/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.81/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.81/1.99      | r1_tarski(X2,X1) != iProver_top
% 11.81/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_869,c_859]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_10272,plain,
% 11.81/1.99      ( k3_subset_1(k1_tops_1(sK1,sK3),k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
% 11.81/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | r1_tarski(X0,sK3) != iProver_top
% 11.81/1.99      | l1_pre_topc(sK1) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_863,c_3236]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_11255,plain,
% 11.81/1.99      ( r1_tarski(X0,sK3) != iProver_top
% 11.81/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | k3_subset_1(k1_tops_1(sK1,sK3),k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_10272,c_25]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_11256,plain,
% 11.81/1.99      ( k3_subset_1(k1_tops_1(sK1,sK3),k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
% 11.81/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | r1_tarski(X0,sK3) != iProver_top ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_11255]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_11267,plain,
% 11.81/1.99      ( k3_subset_1(k1_tops_1(sK1,sK3),k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4))) = k1_tops_1(sK1,sK4)
% 11.81/1.99      | r1_tarski(sK4,sK3) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_1285,c_11256]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_18,negated_conjecture,
% 11.81/1.99      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r1_tarski(sK4,sK3) ),
% 11.81/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_29,plain,
% 11.81/1.99      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 11.81/1.99      | r1_tarski(sK4,sK3) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_11316,plain,
% 11.81/1.99      ( k3_subset_1(k1_tops_1(sK1,sK3),k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4))) = k1_tops_1(sK1,sK4) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_11267,c_24,c_25,c_26,c_29,c_1134,c_1140,c_1178,c_1276]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_11319,plain,
% 11.81/1.99      ( m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
% 11.81/1.99      | r1_tarski(k3_subset_1(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)),k1_tops_1(sK1,sK3)) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_11316,c_860]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1251,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | ~ r1_tarski(X0,sK3)
% 11.81/1.99      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK3))
% 11.81/1.99      | ~ l1_pre_topc(sK1) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1400,plain,
% 11.81/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.81/1.99      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3))
% 11.81/1.99      | ~ r1_tarski(sK4,sK3)
% 11.81/1.99      | ~ l1_pre_topc(sK1) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_1251]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1401,plain,
% 11.81/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 11.81/1.99      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) = iProver_top
% 11.81/1.99      | r1_tarski(sK4,sK3) != iProver_top
% 11.81/1.99      | l1_pre_topc(sK1) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_1400]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_4363,plain,
% 11.81/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK1,sK3)))
% 11.81/1.99      | ~ r1_tarski(X0,k1_tops_1(sK1,sK3)) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_10872,plain,
% 11.81/1.99      ( m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
% 11.81/1.99      | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_4363]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_10873,plain,
% 11.81/1.99      ( m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
% 11.81/1.99      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_10872]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_12691,plain,
% 11.81/1.99      ( m1_subset_1(k1_tops_1(sK1,sK4),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_11319,c_24,c_25,c_26,c_27,c_29,c_1134,c_1140,c_1178,
% 11.81/1.99                 c_1276,c_1401,c_10873]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_41104,plain,
% 11.81/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top ),
% 11.81/1.99      inference(demodulation,[status(thm)],[c_40124,c_12691]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1451,plain,
% 11.81/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3965,plain,
% 11.81/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_tops_1(sK1,sK3)))
% 11.81/1.99      | r1_tarski(sK4,k1_tops_1(sK1,sK3)) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_1451]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3966,plain,
% 11.81/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
% 11.81/1.99      | r1_tarski(sK4,k1_tops_1(sK1,sK3)) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_3965]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_2,plain,
% 11.81/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.81/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1330,plain,
% 11.81/1.99      ( r2_hidden(sK2,X0) | ~ r2_hidden(sK2,sK4) | ~ r1_tarski(sK4,X0) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3215,plain,
% 11.81/1.99      ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 11.81/1.99      | ~ r2_hidden(sK2,sK4)
% 11.81/1.99      | ~ r1_tarski(sK4,k1_tops_1(sK1,sK3)) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_1330]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3216,plain,
% 11.81/1.99      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 11.81/1.99      | r2_hidden(sK2,sK4) != iProver_top
% 11.81/1.99      | r1_tarski(sK4,k1_tops_1(sK1,sK3)) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_3215]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_17,negated_conjecture,
% 11.81/1.99      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r2_hidden(sK2,sK4) ),
% 11.81/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_30,plain,
% 11.81/1.99      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 11.81/1.99      | r2_hidden(sK2,sK4) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(contradiction,plain,
% 11.81/1.99      ( $false ),
% 11.81/1.99      inference(minisat,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_41104,c_3966,c_3216,c_1276,c_1178,c_1140,c_1134,c_30,
% 11.81/1.99                 c_26,c_25,c_24]) ).
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.81/1.99  
% 11.81/1.99  ------                               Statistics
% 11.81/1.99  
% 11.81/1.99  ------ Selected
% 11.81/1.99  
% 11.81/1.99  total_time:                             1.129
% 11.81/1.99  
%------------------------------------------------------------------------------
