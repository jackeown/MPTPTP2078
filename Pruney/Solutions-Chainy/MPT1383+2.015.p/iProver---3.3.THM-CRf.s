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
% DateTime   : Thu Dec  3 12:18:23 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 914 expanded)
%              Number of clauses        :   76 ( 216 expanded)
%              Number of leaves         :   15 ( 254 expanded)
%              Depth                    :   19
%              Number of atoms          :  650 (9373 expanded)
%              Number of equality atoms :  120 ( 232 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

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
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_connsp_2(X2,X0,X1) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X1,X3)
              | ~ r1_tarski(X3,sK2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_connsp_2(sK2,X0,X1) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,sK2)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | m1_connsp_2(sK2,X0,X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(sK1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,sK1) )
            & ( ? [X4] :
                  ( r2_hidden(sK1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | m1_connsp_2(X2,X0,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | m1_connsp_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,sK0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ m1_connsp_2(X2,sK0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | m1_connsp_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ m1_connsp_2(sK2,sK0,sK1) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | m1_connsp_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f43,f42,f41,f40])).

fof(f63,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                    & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ~ m1_connsp_2(X3,X0,X1)
                      | ~ m1_connsp_2(X2,X0,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                    & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ~ m1_connsp_2(X3,X0,X1)
                      | ~ m1_connsp_2(X2,X0,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(X3,X0,X1)
      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_917,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_921,plain,
    ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_918,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,negated_conjecture,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ v3_pre_topc(X0,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_923,plain,
    ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r2_hidden(sK1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1262,plain,
    ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_923])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_28,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1208,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1209,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1233,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1234,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_6,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1236,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1237,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_1369,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1370,plain,
    ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_257,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_10])).

cnf(c_258,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_1292,plain,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_1378,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_1379,plain,
    ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1378])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1364,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1518,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_1519,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1567,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1568,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_1870,plain,
    ( m1_connsp_2(sK2,sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1262,c_25,c_26,c_27,c_28,c_29,c_1209,c_1234,c_1237,c_1370,c_1379,c_1519,c_1568])).

cnf(c_1876,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_1870])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_934,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1998,plain,
    ( k3_xboole_0(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_1876,c_934])).

cnf(c_932,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1483,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_932])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_163,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_164,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_163])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_164])).

cnf(c_913,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_2156,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_1483,c_913])).

cnf(c_11,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X1),X3,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_926,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | m1_connsp_2(k9_subset_1(u1_struct_0(X1),X3,X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3574,plain,
    ( m1_connsp_2(k3_xboole_0(X0,sK2),sK0,X1) != iProver_top
    | m1_connsp_2(sK2,sK0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2156,c_926])).

cnf(c_11348,plain,
    ( m1_connsp_2(k3_xboole_0(X0,sK2),sK0,X1) != iProver_top
    | m1_connsp_2(sK2,sK0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3574,c_25,c_26,c_27,c_29])).

cnf(c_11362,plain,
    ( m1_connsp_2(sK3,sK0,X0) != iProver_top
    | m1_connsp_2(sK2,sK0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1998,c_11348])).

cnf(c_19,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_919,plain,
    ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_30,plain,
    ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1643,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_919,c_25,c_26,c_27,c_28,c_29,c_30,c_1209,c_1234,c_1237,c_1370,c_1379,c_1519,c_1568])).

cnf(c_11440,plain,
    ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_connsp_2(sK2,sK0,X0) = iProver_top
    | m1_connsp_2(sK3,sK0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11362,c_25,c_26,c_27,c_28,c_29,c_30,c_1209,c_1234,c_1237,c_1370,c_1379,c_1519,c_1568])).

cnf(c_11441,plain,
    ( m1_connsp_2(sK3,sK0,X0) != iProver_top
    | m1_connsp_2(sK2,sK0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11440])).

cnf(c_11449,plain,
    ( m1_connsp_2(sK3,sK0,sK1) != iProver_top
    | m1_connsp_2(sK2,sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_11441])).

cnf(c_14,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1943,plain,
    ( m1_connsp_2(sK3,X0,sK1)
    | ~ v3_pre_topc(sK3,X0)
    | ~ r2_hidden(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1944,plain,
    ( m1_connsp_2(sK3,X0,sK1) = iProver_top
    | v3_pre_topc(sK3,X0) != iProver_top
    | r2_hidden(sK1,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1943])).

cnf(c_1946,plain,
    ( m1_connsp_2(sK3,sK0,sK1) = iProver_top
    | v3_pre_topc(sK3,sK0) != iProver_top
    | r2_hidden(sK1,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_16,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_33,plain,
    ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v3_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,plain,
    ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
    | v3_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11449,c_1946,c_1870,c_1643,c_33,c_31,c_28,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.91/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/0.99  
% 3.91/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.91/0.99  
% 3.91/0.99  ------  iProver source info
% 3.91/0.99  
% 3.91/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.91/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.91/0.99  git: non_committed_changes: false
% 3.91/0.99  git: last_make_outside_of_git: false
% 3.91/0.99  
% 3.91/0.99  ------ 
% 3.91/0.99  ------ Parsing...
% 3.91/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.91/0.99  ------ Proving...
% 3.91/0.99  ------ Problem Properties 
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  clauses                                 25
% 3.91/0.99  conjectures                             10
% 3.91/0.99  EPR                                     7
% 3.91/0.99  Horn                                    14
% 3.91/0.99  unary                                   5
% 3.91/0.99  binary                                  8
% 3.91/0.99  lits                                    90
% 3.91/0.99  lits eq                                 2
% 3.91/0.99  fd_pure                                 0
% 3.91/0.99  fd_pseudo                               0
% 3.91/0.99  fd_cond                                 0
% 3.91/0.99  fd_pseudo_cond                          0
% 3.91/0.99  AC symbols                              0
% 3.91/0.99  
% 3.91/0.99  ------ Input Options Time Limit: Unbounded
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  ------ 
% 3.91/0.99  Current options:
% 3.91/0.99  ------ 
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  ------ Proving...
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  % SZS status Theorem for theBenchmark.p
% 3.91/0.99  
% 3.91/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.91/0.99  
% 3.91/0.99  fof(f12,conjecture,(
% 3.91/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f13,negated_conjecture,(
% 3.91/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.91/0.99    inference(negated_conjecture,[],[f12])).
% 3.91/0.99  
% 3.91/0.99  fof(f31,plain,(
% 3.91/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.91/0.99    inference(ennf_transformation,[],[f13])).
% 3.91/0.99  
% 3.91/0.99  fof(f32,plain,(
% 3.91/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.91/0.99    inference(flattening,[],[f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f37,plain,(
% 3.91/0.99    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.91/0.99    inference(nnf_transformation,[],[f32])).
% 3.91/0.99  
% 3.91/0.99  fof(f38,plain,(
% 3.91/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.91/0.99    inference(flattening,[],[f37])).
% 3.91/0.99  
% 3.91/0.99  fof(f39,plain,(
% 3.91/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.91/0.99    inference(rectify,[],[f38])).
% 3.91/0.99  
% 3.91/0.99  fof(f43,plain,(
% 3.91/0.99    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3) & r1_tarski(sK3,X2) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.91/0.99    introduced(choice_axiom,[])).
% 3.91/0.99  
% 3.91/0.99  fof(f42,plain,(
% 3.91/0.99    ( ! [X0,X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(sK2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(sK2,X0,X1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.91/0.99    introduced(choice_axiom,[])).
% 3.91/0.99  
% 3.91/0.99  fof(f41,plain,(
% 3.91/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 3.91/0.99    introduced(choice_axiom,[])).
% 3.91/0.99  
% 3.91/0.99  fof(f40,plain,(
% 3.91/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.91/0.99    introduced(choice_axiom,[])).
% 3.91/0.99  
% 3.91/0.99  fof(f44,plain,(
% 3.91/0.99    (((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(sK2,sK0,sK1)) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.91/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f43,f42,f41,f40])).
% 3.91/0.99  
% 3.91/0.99  fof(f63,plain,(
% 3.91/0.99    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.91/0.99    inference(cnf_transformation,[],[f44])).
% 3.91/0.99  
% 3.91/0.99  fof(f67,plain,(
% 3.91/0.99    r1_tarski(sK3,sK2) | m1_connsp_2(sK2,sK0,sK1)),
% 3.91/0.99    inference(cnf_transformation,[],[f44])).
% 3.91/0.99  
% 3.91/0.99  fof(f64,plain,(
% 3.91/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.91/0.99    inference(cnf_transformation,[],[f44])).
% 3.91/0.99  
% 3.91/0.99  fof(f69,plain,(
% 3.91/0.99    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(sK2,sK0,sK1)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f44])).
% 3.91/0.99  
% 3.91/0.99  fof(f60,plain,(
% 3.91/0.99    ~v2_struct_0(sK0)),
% 3.91/0.99    inference(cnf_transformation,[],[f44])).
% 3.91/0.99  
% 3.91/0.99  fof(f61,plain,(
% 3.91/0.99    v2_pre_topc(sK0)),
% 3.91/0.99    inference(cnf_transformation,[],[f44])).
% 3.91/0.99  
% 3.91/0.99  fof(f62,plain,(
% 3.91/0.99    l1_pre_topc(sK0)),
% 3.91/0.99    inference(cnf_transformation,[],[f44])).
% 3.91/0.99  
% 3.91/0.99  fof(f4,axiom,(
% 3.91/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f33,plain,(
% 3.91/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.91/0.99    inference(nnf_transformation,[],[f4])).
% 3.91/0.99  
% 3.91/0.99  fof(f48,plain,(
% 3.91/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.91/0.99    inference(cnf_transformation,[],[f33])).
% 3.91/0.99  
% 3.91/0.99  fof(f7,axiom,(
% 3.91/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f22,plain,(
% 3.91/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/0.99    inference(ennf_transformation,[],[f7])).
% 3.91/0.99  
% 3.91/0.99  fof(f52,plain,(
% 3.91/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f22])).
% 3.91/0.99  
% 3.91/0.99  fof(f6,axiom,(
% 3.91/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f20,plain,(
% 3.91/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.91/0.99    inference(ennf_transformation,[],[f6])).
% 3.91/0.99  
% 3.91/0.99  fof(f21,plain,(
% 3.91/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/0.99    inference(flattening,[],[f20])).
% 3.91/0.99  
% 3.91/0.99  fof(f51,plain,(
% 3.91/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f21])).
% 3.91/0.99  
% 3.91/0.99  fof(f8,axiom,(
% 3.91/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f23,plain,(
% 3.91/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.91/0.99    inference(ennf_transformation,[],[f8])).
% 3.91/0.99  
% 3.91/0.99  fof(f24,plain,(
% 3.91/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/0.99    inference(flattening,[],[f23])).
% 3.91/0.99  
% 3.91/0.99  fof(f34,plain,(
% 3.91/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/0.99    inference(nnf_transformation,[],[f24])).
% 3.91/0.99  
% 3.91/0.99  fof(f53,plain,(
% 3.91/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f34])).
% 3.91/0.99  
% 3.91/0.99  fof(f9,axiom,(
% 3.91/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f25,plain,(
% 3.91/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.91/0.99    inference(ennf_transformation,[],[f9])).
% 3.91/0.99  
% 3.91/0.99  fof(f26,plain,(
% 3.91/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/0.99    inference(flattening,[],[f25])).
% 3.91/0.99  
% 3.91/0.99  fof(f55,plain,(
% 3.91/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f26])).
% 3.91/0.99  
% 3.91/0.99  fof(f1,axiom,(
% 3.91/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f14,plain,(
% 3.91/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.91/0.99    inference(ennf_transformation,[],[f1])).
% 3.91/0.99  
% 3.91/0.99  fof(f15,plain,(
% 3.91/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.91/0.99    inference(flattening,[],[f14])).
% 3.91/0.99  
% 3.91/0.99  fof(f45,plain,(
% 3.91/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f15])).
% 3.91/0.99  
% 3.91/0.99  fof(f49,plain,(
% 3.91/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f33])).
% 3.91/0.99  
% 3.91/0.99  fof(f2,axiom,(
% 3.91/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f16,plain,(
% 3.91/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.91/0.99    inference(ennf_transformation,[],[f2])).
% 3.91/0.99  
% 3.91/0.99  fof(f46,plain,(
% 3.91/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f16])).
% 3.91/0.99  
% 3.91/0.99  fof(f3,axiom,(
% 3.91/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f17,plain,(
% 3.91/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f3])).
% 3.91/1.00  
% 3.91/1.00  fof(f47,plain,(
% 3.91/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.91/1.00    inference(cnf_transformation,[],[f17])).
% 3.91/1.00  
% 3.91/1.00  fof(f10,axiom,(
% 3.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f27,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f10])).
% 3.91/1.00  
% 3.91/1.00  fof(f28,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(flattening,[],[f27])).
% 3.91/1.00  
% 3.91/1.00  fof(f35,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) | ~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | (~m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(X2,X0,X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(nnf_transformation,[],[f28])).
% 3.91/1.00  
% 3.91/1.00  fof(f36,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) | ~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | ~m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(flattening,[],[f35])).
% 3.91/1.00  
% 3.91/1.00  fof(f58,plain,(
% 3.91/1.00    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f36])).
% 3.91/1.00  
% 3.91/1.00  fof(f65,plain,(
% 3.91/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1)),
% 3.91/1.00    inference(cnf_transformation,[],[f44])).
% 3.91/1.00  
% 3.91/1.00  fof(f11,axiom,(
% 3.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f29,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f11])).
% 3.91/1.00  
% 3.91/1.00  fof(f30,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(flattening,[],[f29])).
% 3.91/1.00  
% 3.91/1.00  fof(f59,plain,(
% 3.91/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f30])).
% 3.91/1.00  
% 3.91/1.00  fof(f68,plain,(
% 3.91/1.00    r2_hidden(sK1,sK3) | m1_connsp_2(sK2,sK0,sK1)),
% 3.91/1.00    inference(cnf_transformation,[],[f44])).
% 3.91/1.00  
% 3.91/1.00  fof(f66,plain,(
% 3.91/1.00    v3_pre_topc(sK3,sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 3.91/1.00    inference(cnf_transformation,[],[f44])).
% 3.91/1.00  
% 3.91/1.00  cnf(c_21,negated_conjecture,
% 3.91/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 3.91/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_917,plain,
% 3.91/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_17,negated_conjecture,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) | r1_tarski(sK3,sK2) ),
% 3.91/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_921,plain,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
% 3.91/1.00      | r1_tarski(sK3,sK2) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_20,negated_conjecture,
% 3.91/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.91/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_918,plain,
% 3.91/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_15,negated_conjecture,
% 3.91/1.00      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 3.91/1.00      | ~ v3_pre_topc(X0,sK0)
% 3.91/1.00      | ~ r2_hidden(sK1,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.91/1.00      | ~ r1_tarski(X0,sK2) ),
% 3.91/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_923,plain,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
% 3.91/1.00      | v3_pre_topc(X0,sK0) != iProver_top
% 3.91/1.00      | r2_hidden(sK1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | r1_tarski(X0,sK2) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1262,plain,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
% 3.91/1.00      | v3_pre_topc(sK2,sK0) != iProver_top
% 3.91/1.00      | r2_hidden(sK1,sK2) != iProver_top
% 3.91/1.00      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_918,c_923]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_24,negated_conjecture,
% 3.91/1.00      ( ~ v2_struct_0(sK0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_25,plain,
% 3.91/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_23,negated_conjecture,
% 3.91/1.00      ( v2_pre_topc(sK0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_26,plain,
% 3.91/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_22,negated_conjecture,
% 3.91/1.00      ( l1_pre_topc(sK0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_27,plain,
% 3.91/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_28,plain,
% 3.91/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_29,plain,
% 3.91/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1208,plain,
% 3.91/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.91/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1209,plain,
% 3.91/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_7,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1233,plain,
% 3.91/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.91/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.91/1.00      | ~ l1_pre_topc(sK0) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1234,plain,
% 3.91/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6,plain,
% 3.91/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | ~ v2_pre_topc(X0)
% 3.91/1.00      | ~ l1_pre_topc(X0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1236,plain,
% 3.91/1.00      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 3.91/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.91/1.00      | ~ v2_pre_topc(sK0)
% 3.91/1.00      | ~ l1_pre_topc(sK0) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1237,plain,
% 3.91/1.00      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0) = iProver_top
% 3.91/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1236]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1369,plain,
% 3.91/1.00      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 3.91/1.00      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 3.91/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.91/1.00      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.91/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1370,plain,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
% 3.91/1.00      | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) != iProver_top
% 3.91/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 3.91/1.00      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_9,plain,
% 3.91/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.91/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.91/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_10,plain,
% 3.91/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.91/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_257,plain,
% 3.91/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.91/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.91/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_9,c_10]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_258,plain,
% 3.91/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.91/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.91/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(renaming,[status(thm)],[c_257]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1292,plain,
% 3.91/1.00      ( ~ m1_connsp_2(X0,sK0,sK1)
% 3.91/1.00      | r2_hidden(sK1,k1_tops_1(sK0,X0))
% 3.91/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 3.91/1.00      | v2_struct_0(sK0)
% 3.91/1.00      | ~ v2_pre_topc(sK0)
% 3.91/1.00      | ~ l1_pre_topc(sK0) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_258]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1378,plain,
% 3.91/1.00      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 3.91/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.91/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 3.91/1.00      | v2_struct_0(sK0)
% 3.91/1.00      | ~ v2_pre_topc(sK0)
% 3.91/1.00      | ~ l1_pre_topc(sK0) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_1292]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1379,plain,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
% 3.91/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 3.91/1.00      | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
% 3.91/1.00      | v2_struct_0(sK0) = iProver_top
% 3.91/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1378]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_0,plain,
% 3.91/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1364,plain,
% 3.91/1.00      ( r1_tarski(k1_tops_1(sK0,sK2),X0)
% 3.91/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.91/1.00      | ~ r1_tarski(sK2,X0) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1518,plain,
% 3.91/1.00      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 3.91/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.91/1.00      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_1364]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1519,plain,
% 3.91/1.00      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top
% 3.91/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.91/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3,plain,
% 3.91/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1567,plain,
% 3.91/1.00      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.91/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1568,plain,
% 3.91/1.00      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.91/1.00      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1870,plain,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_1262,c_25,c_26,c_27,c_28,c_29,c_1209,c_1234,c_1237,
% 3.91/1.00                 c_1370,c_1379,c_1519,c_1568]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1876,plain,
% 3.91/1.00      ( r1_tarski(sK3,sK2) = iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_921,c_1870]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1,plain,
% 3.91/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.91/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_934,plain,
% 3.91/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1998,plain,
% 3.91/1.00      ( k3_xboole_0(sK3,sK2) = sK3 ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_1876,c_934]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_932,plain,
% 3.91/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.91/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1483,plain,
% 3.91/1.00      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_918,c_932]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_2,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.91/1.00      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_163,plain,
% 3.91/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.91/1.00      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_164,plain,
% 3.91/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.91/1.00      inference(renaming,[status(thm)],[c_163]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_213,plain,
% 3.91/1.00      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.91/1.00      inference(bin_hyper_res,[status(thm)],[c_2,c_164]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_913,plain,
% 3.91/1.00      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.91/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_2156,plain,
% 3.91/1.00      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_1483,c_913]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_11,plain,
% 3.91/1.00      ( m1_connsp_2(X0,X1,X2)
% 3.91/1.00      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X1),X3,X0),X1,X2)
% 3.91/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.91/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_926,plain,
% 3.91/1.00      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 3.91/1.00      | m1_connsp_2(k9_subset_1(u1_struct_0(X1),X3,X0),X1,X2) != iProver_top
% 3.91/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.91/1.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.91/1.00      | v2_struct_0(X1) = iProver_top
% 3.91/1.00      | v2_pre_topc(X1) != iProver_top
% 3.91/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3574,plain,
% 3.91/1.00      ( m1_connsp_2(k3_xboole_0(X0,sK2),sK0,X1) != iProver_top
% 3.91/1.00      | m1_connsp_2(sK2,sK0,X1) = iProver_top
% 3.91/1.00      | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | v2_struct_0(sK0) = iProver_top
% 3.91/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_2156,c_926]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_11348,plain,
% 3.91/1.00      ( m1_connsp_2(k3_xboole_0(X0,sK2),sK0,X1) != iProver_top
% 3.91/1.00      | m1_connsp_2(sK2,sK0,X1) = iProver_top
% 3.91/1.00      | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_3574,c_25,c_26,c_27,c_29]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_11362,plain,
% 3.91/1.00      ( m1_connsp_2(sK3,sK0,X0) != iProver_top
% 3.91/1.00      | m1_connsp_2(sK2,sK0,X0) = iProver_top
% 3.91/1.00      | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 3.91/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_1998,c_11348]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_19,negated_conjecture,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1)
% 3.91/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.91/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_919,plain,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
% 3.91/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_30,plain,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
% 3.91/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1643,plain,
% 3.91/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_919,c_25,c_26,c_27,c_28,c_29,c_30,c_1209,c_1234,
% 3.91/1.00                 c_1237,c_1370,c_1379,c_1519,c_1568]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_11440,plain,
% 3.91/1.00      ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 3.91/1.00      | m1_connsp_2(sK2,sK0,X0) = iProver_top
% 3.91/1.00      | m1_connsp_2(sK3,sK0,X0) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_11362,c_25,c_26,c_27,c_28,c_29,c_30,c_1209,c_1234,
% 3.91/1.00                 c_1237,c_1370,c_1379,c_1519,c_1568]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_11441,plain,
% 3.91/1.00      ( m1_connsp_2(sK3,sK0,X0) != iProver_top
% 3.91/1.00      | m1_connsp_2(sK2,sK0,X0) = iProver_top
% 3.91/1.00      | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.91/1.00      inference(renaming,[status(thm)],[c_11440]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_11449,plain,
% 3.91/1.00      ( m1_connsp_2(sK3,sK0,sK1) != iProver_top
% 3.91/1.00      | m1_connsp_2(sK2,sK0,sK1) = iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_917,c_11441]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_14,plain,
% 3.91/1.00      ( m1_connsp_2(X0,X1,X2)
% 3.91/1.00      | ~ v3_pre_topc(X0,X1)
% 3.91/1.00      | ~ r2_hidden(X2,X0)
% 3.91/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1943,plain,
% 3.91/1.00      ( m1_connsp_2(sK3,X0,sK1)
% 3.91/1.00      | ~ v3_pre_topc(sK3,X0)
% 3.91/1.00      | ~ r2_hidden(sK1,sK3)
% 3.91/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | ~ m1_subset_1(sK1,u1_struct_0(X0))
% 3.91/1.00      | v2_struct_0(X0)
% 3.91/1.00      | ~ v2_pre_topc(X0)
% 3.91/1.00      | ~ l1_pre_topc(X0) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1944,plain,
% 3.91/1.00      ( m1_connsp_2(sK3,X0,sK1) = iProver_top
% 3.91/1.00      | v3_pre_topc(sK3,X0) != iProver_top
% 3.91/1.00      | r2_hidden(sK1,sK3) != iProver_top
% 3.91/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.91/1.00      | m1_subset_1(sK1,u1_struct_0(X0)) != iProver_top
% 3.91/1.00      | v2_struct_0(X0) = iProver_top
% 3.91/1.00      | v2_pre_topc(X0) != iProver_top
% 3.91/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1943]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1946,plain,
% 3.91/1.00      ( m1_connsp_2(sK3,sK0,sK1) = iProver_top
% 3.91/1.00      | v3_pre_topc(sK3,sK0) != iProver_top
% 3.91/1.00      | r2_hidden(sK1,sK3) != iProver_top
% 3.91/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
% 3.91/1.00      | v2_struct_0(sK0) = iProver_top
% 3.91/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_1944]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_16,negated_conjecture,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) | r2_hidden(sK1,sK3) ),
% 3.91/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_33,plain,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
% 3.91/1.00      | r2_hidden(sK1,sK3) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_18,negated_conjecture,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) | v3_pre_topc(sK3,sK0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_31,plain,
% 3.91/1.00      ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
% 3.91/1.00      | v3_pre_topc(sK3,sK0) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(contradiction,plain,
% 3.91/1.00      ( $false ),
% 3.91/1.00      inference(minisat,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_11449,c_1946,c_1870,c_1643,c_33,c_31,c_28,c_27,c_26,
% 3.91/1.00                 c_25]) ).
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.91/1.00  
% 3.91/1.00  ------                               Statistics
% 3.91/1.00  
% 3.91/1.00  ------ Selected
% 3.91/1.00  
% 3.91/1.00  total_time:                             0.502
% 3.91/1.00  
%------------------------------------------------------------------------------
