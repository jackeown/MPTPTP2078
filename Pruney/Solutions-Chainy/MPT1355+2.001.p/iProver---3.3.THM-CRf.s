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
% DateTime   : Thu Dec  3 12:17:54 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 769 expanded)
%              Number of clauses        :  123 ( 199 expanded)
%              Number of leaves         :   15 ( 172 expanded)
%              Depth                    :   18
%              Number of atoms          :  917 (5289 expanded)
%              Number of equality atoms :   69 (  81 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ~ ( v1_finset_1(X2)
                        & m1_setfam_1(X2,u1_struct_0(X0))
                        & r1_tarski(X2,X1) ) )
                & v1_tops_2(X1,X0)
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( v1_finset_1(X2)
                & m1_setfam_1(X2,u1_struct_0(X0))
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X1,X0)
            | ~ m1_setfam_1(X1,u1_struct_0(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( v1_finset_1(X2)
                & m1_setfam_1(X2,u1_struct_0(X0))
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X1,X0)
            | ~ m1_setfam_1(X1,u1_struct_0(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ v1_finset_1(X2)
                  | ~ m1_setfam_1(X2,u1_struct_0(X0))
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & v1_tops_2(X1,X0)
              & m1_setfam_1(X1,u1_struct_0(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( v1_finset_1(X2)
                  & m1_setfam_1(X2,u1_struct_0(X0))
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_setfam_1(X1,u1_struct_0(X0))
              | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ v1_finset_1(X2)
                  | ~ m1_setfam_1(X2,u1_struct_0(X0))
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & v1_tops_2(X1,X0)
              & m1_setfam_1(X1,u1_struct_0(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( v1_finset_1(X4)
                  & m1_setfam_1(X4,u1_struct_0(X0))
                  & r1_tarski(X4,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X3,X0)
              | ~ m1_setfam_1(X3,u1_struct_0(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f16])).

fof(f19,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( v1_finset_1(X4)
          & m1_setfam_1(X4,u1_struct_0(X0))
          & r1_tarski(X4,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( v1_finset_1(sK1(X0,X3))
        & m1_setfam_1(sK1(X0,X3),u1_struct_0(X0))
        & r1_tarski(sK1(X0,X3),X3)
        & m1_subset_1(sK1(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v1_finset_1(X2)
              | ~ m1_setfam_1(X2,u1_struct_0(X0))
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X1,X0)
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X2] :
            ( ~ v1_finset_1(X2)
            | ~ m1_setfam_1(X2,u1_struct_0(X0))
            | ~ r1_tarski(X2,sK0(X0))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK0(X0),X0)
        & m1_setfam_1(sK0(X0),u1_struct_0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ v1_finset_1(X2)
                | ~ m1_setfam_1(X2,u1_struct_0(X0))
                | ~ r1_tarski(X2,sK0(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & v1_tops_2(sK0(X0),X0)
            & m1_setfam_1(sK0(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X3] :
              ( ( v1_finset_1(sK1(X0,X3))
                & m1_setfam_1(sK1(X0,X3),u1_struct_0(X0))
                & r1_tarski(sK1(X0,X3),X3)
                & m1_subset_1(sK1(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X3,X0)
              | ~ m1_setfam_1(X3,u1_struct_0(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f35,plain,(
    ! [X0,X3] :
      ( m1_setfam_1(sK1(X0,X3),u1_struct_0(X0))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ( v1_compts_1(X0)
        <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> v2_compts_1(k2_struct_0(X0),X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ? [X0] :
      ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
        | ~ v1_compts_1(X0) )
      & ( v2_compts_1(k2_struct_0(X0),X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0] :
      ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
        | ~ v1_compts_1(X0) )
      & ( v2_compts_1(k2_struct_0(X0),X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0] :
        ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | v1_compts_1(X0) )
        & l1_pre_topc(X0) )
   => ( ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
        | ~ v1_compts_1(sK4) )
      & ( v2_compts_1(k2_struct_0(sK4),sK4)
        | v1_compts_1(sK4) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
      | ~ v1_compts_1(sK4) )
    & ( v2_compts_1(k2_struct_0(sK4),sK4)
      | v1_compts_1(sK4) )
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f49,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ~ ( v1_finset_1(X3)
                            & m1_setfam_1(X3,X1)
                            & r1_tarski(X3,X2) ) )
                    & v1_tops_2(X2,X0)
                    & m1_setfam_1(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( v1_finset_1(X3)
                      & m1_setfam_1(X3,X1)
                      & r1_tarski(X3,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X2,X0)
                  | ~ m1_setfam_1(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( v1_finset_1(X5)
                      & m1_setfam_1(X5,X1)
                      & r1_tarski(X5,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f21])).

fof(f24,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( v1_finset_1(X5)
          & m1_setfam_1(X5,X1)
          & r1_tarski(X5,X4)
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( v1_finset_1(sK3(X0,X1,X4))
        & m1_setfam_1(sK3(X0,X1,X4),X1)
        & r1_tarski(sK3(X0,X1,X4),X4)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ v1_finset_1(X3)
              | ~ m1_setfam_1(X3,X1)
              | ~ r1_tarski(X3,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X2,X0)
          & m1_setfam_1(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X3] :
            ( ~ v1_finset_1(X3)
            | ~ m1_setfam_1(X3,X1)
            | ~ r1_tarski(X3,sK2(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK2(X0,X1),X0)
        & m1_setfam_1(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ( ! [X3] :
                    ( ~ v1_finset_1(X3)
                    | ~ m1_setfam_1(X3,X1)
                    | ~ r1_tarski(X3,sK2(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & v1_tops_2(sK2(X0,X1),X0)
                & m1_setfam_1(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ( v1_finset_1(sK3(X0,X1,X4))
                    & m1_setfam_1(sK3(X0,X1,X4),X1)
                    & r1_tarski(sK3(X0,X1,X4),X4)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f24,f23])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( m1_setfam_1(sK3(X0,X1,X4),X1)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X4),X4)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ v1_finset_1(X2)
      | ~ m1_setfam_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X2,sK0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v1_tops_2(sK0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( v1_finset_1(sK3(X0,X1,X4))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v1_finset_1(X3)
      | ~ m1_setfam_1(X3,X1)
      | ~ r1_tarski(X3,sK2(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X0,X3] :
      ( r1_tarski(sK1(X0,X3),X3)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | v1_tops_2(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X0,X3] :
      ( v1_finset_1(sK1(X0,X3))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK1(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | m1_setfam_1(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,
    ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | m1_setfam_1(sK0(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,
    ( v2_compts_1(k2_struct_0(sK4),sK4)
    | v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_8,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | m1_setfam_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_925,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | m1_setfam_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_926,plain,
    ( ~ v1_tops_2(X0,sK4)
    | ~ m1_setfam_1(X0,u1_struct_0(sK4))
    | m1_setfam_1(sK1(sK4,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_925])).

cnf(c_4854,plain,
    ( ~ v1_tops_2(X0_45,sK4)
    | ~ m1_setfam_1(X0_45,u1_struct_0(sK4))
    | m1_setfam_1(sK1(sK4,X0_45),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_926])).

cnf(c_6154,plain,
    ( ~ v1_tops_2(sK2(sK4,u1_struct_0(sK4)),sK4)
    | ~ m1_setfam_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4))
    | m1_setfam_1(sK1(sK4,sK2(sK4,u1_struct_0(sK4))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_compts_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4854])).

cnf(c_4876,plain,
    ( ~ v2_compts_1(X0_45,X0_46)
    | v2_compts_1(X1_45,X0_46)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_5782,plain,
    ( v2_compts_1(X0_45,sK4)
    | ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | X0_45 != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4876])).

cnf(c_6078,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4)
    | ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | u1_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5782])).

cnf(c_16,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,X0)
    | m1_setfam_1(sK3(X1,X0,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_766,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,X0)
    | m1_setfam_1(sK3(X1,X0,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_767,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_setfam_1(X1,X0)
    | m1_setfam_1(sK3(sK4,X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_4859,plain,
    ( ~ v2_compts_1(X0_45,sK4)
    | ~ v1_tops_2(X1_45,sK4)
    | ~ m1_setfam_1(X1_45,X0_45)
    | m1_setfam_1(sK3(sK4,X0_45,X1_45),X0_45)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_767])).

cnf(c_5651,plain,
    ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
    | ~ v1_tops_2(X0_45,sK4)
    | ~ m1_setfam_1(X0_45,u1_struct_0(sK4))
    | m1_setfam_1(sK3(sK4,u1_struct_0(sK4),X0_45),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_4859])).

cnf(c_6072,plain,
    ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
    | ~ v1_tops_2(sK0(sK4),sK4)
    | m1_setfam_1(sK3(sK4,u1_struct_0(sK4),sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_5651])).

cnf(c_5665,plain,
    ( v2_compts_1(X0_45,sK4)
    | ~ v2_compts_1(u1_struct_0(sK4),sK4)
    | X0_45 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4876])).

cnf(c_6001,plain,
    ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
    | v2_compts_1(k2_struct_0(sK4),sK4)
    | k2_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5665])).

cnf(c_4870,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_5645,plain,
    ( X0_45 != X1_45
    | k2_struct_0(sK4) != X1_45
    | k2_struct_0(sK4) = X0_45 ),
    inference(instantiation,[status(thm)],[c_4870])).

cnf(c_5731,plain,
    ( X0_45 != k2_struct_0(sK4)
    | k2_struct_0(sK4) = X0_45
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5645])).

cnf(c_5896,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | k2_struct_0(sK4) = u1_struct_0(sK4)
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5731])).

cnf(c_17,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | r1_tarski(sK3(X1,X0,X2),X2)
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_742,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | r1_tarski(sK3(X1,X0,X2),X2)
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_743,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | r1_tarski(sK3(sK4,X0,X1),X1)
    | ~ m1_setfam_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,sK0(X1))
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_finset_1(X0)
    | v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_967,plain,
    ( ~ r1_tarski(X0,sK0(X1))
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_finset_1(X0)
    | v1_compts_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_968,plain,
    ( ~ r1_tarski(X0,sK0(sK4))
    | ~ m1_setfam_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_finset_1(X0)
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_967])).

cnf(c_3375,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_setfam_1(X1,X0)
    | ~ m1_setfam_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_finset_1(X2)
    | v1_compts_1(sK4)
    | sK3(sK4,X0,X1) != X2
    | sK0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_743,c_968])).

cnf(c_3376,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(sK0(sK4),sK4)
    | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_finset_1(sK3(sK4,X0,sK0(sK4)))
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_3375])).

cnf(c_6,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_62,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( v1_tops_2(sK0(X0),X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_68,plain,
    ( v1_tops_2(sK0(sK4),sK4)
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1242,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_setfam_1(X1,X0)
    | ~ m1_setfam_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_finset_1(X2)
    | v1_compts_1(sK4)
    | sK3(sK4,X0,X1) != X2
    | sK0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_743,c_968])).

cnf(c_1243,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(sK0(sK4),sK4)
    | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_finset_1(sK3(sK4,X0,sK0(sK4)))
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1242])).

cnf(c_708,plain,
    ( v1_tops_2(sK0(X0),X0)
    | v1_compts_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_709,plain,
    ( v1_tops_2(sK0(sK4),sK4)
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_15,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_finset_1(sK3(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_790,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_finset_1(sK3(X1,X0,X2))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_791,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_setfam_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_finset_1(sK3(sK4,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_790])).

cnf(c_1332,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_finset_1(sK3(sK4,X0,X1))
    | v1_compts_1(sK4)
    | sK0(sK4) != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_709,c_791])).

cnf(c_1333,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_finset_1(sK3(sK4,X0,sK0(sK4)))
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1332])).

cnf(c_1337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ v2_compts_1(X0,sK4)
    | v1_finset_1(sK3(sK4,X0,sK0(sK4)))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1333,c_21,c_62])).

cnf(c_1338,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_finset_1(sK3(sK4,X0,sK0(sK4)))
    | v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_1337])).

cnf(c_18,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_718,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_719,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_setfam_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_1413,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_compts_1(sK4)
    | sK0(sK4) != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_709,c_719])).

cnf(c_1414,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1413])).

cnf(c_1418,plain,
    ( m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ v2_compts_1(X0,sK4)
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1414,c_21,c_62])).

cnf(c_1419,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_1418])).

cnf(c_3378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
    | ~ v2_compts_1(X0,sK4)
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3376,c_21,c_62,c_68,c_1243,c_1338,c_1419])).

cnf(c_3379,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_3378])).

cnf(c_4852,plain,
    ( ~ v2_compts_1(X0_45,sK4)
    | ~ m1_setfam_1(sK3(sK4,X0_45,sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),X0_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_3379])).

cnf(c_5866,plain,
    ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
    | ~ m1_setfam_1(sK3(sK4,u1_struct_0(sK4),sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_compts_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4852])).

cnf(c_4869,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_5647,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4869])).

cnf(c_11,plain,
    ( v2_compts_1(X0,X1)
    | ~ r1_tarski(X2,sK2(X1,X0))
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_finset_1(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_859,plain,
    ( v2_compts_1(X0,X1)
    | ~ r1_tarski(X2,sK2(X1,X0))
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_finset_1(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_860,plain,
    ( v2_compts_1(X0,sK4)
    | ~ r1_tarski(X1,sK2(sK4,X0))
    | ~ m1_setfam_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_finset_1(X1) ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_9,plain,
    ( ~ v1_tops_2(X0,X1)
    | r1_tarski(sK1(X1,X0),X0)
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_904,plain,
    ( ~ v1_tops_2(X0,X1)
    | r1_tarski(sK1(X1,X0),X0)
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_905,plain,
    ( ~ v1_tops_2(X0,sK4)
    | r1_tarski(sK1(sK4,X0),X0)
    | ~ m1_setfam_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_3400,plain,
    ( v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_setfam_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_finset_1(X2)
    | ~ v1_compts_1(sK4)
    | sK2(sK4,X0) != X1
    | sK1(sK4,X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_860,c_905])).

cnf(c_3401,plain,
    ( v2_compts_1(X0,sK4)
    | ~ v1_tops_2(sK2(sK4,X0),sK4)
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK1(sK4,sK2(sK4,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_finset_1(sK1(sK4,sK2(sK4,X0)))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_3400])).

cnf(c_14,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_814,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_815,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_12,plain,
    ( v2_compts_1(X0,X1)
    | v1_tops_2(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_844,plain,
    ( v2_compts_1(X0,X1)
    | v1_tops_2(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_845,plain,
    ( v2_compts_1(X0,sK4)
    | v1_tops_2(sK2(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_1275,plain,
    ( v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_setfam_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_finset_1(X2)
    | ~ v1_compts_1(sK4)
    | sK2(sK4,X0) != X1
    | sK1(sK4,X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_860,c_905])).

cnf(c_1276,plain,
    ( v2_compts_1(X0,sK4)
    | ~ v1_tops_2(sK2(sK4,X0),sK4)
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK1(sK4,sK2(sK4,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_finset_1(sK1(sK4,sK2(sK4,X0)))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1275])).

cnf(c_7,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v1_finset_1(sK1(X1,X0))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_946,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v1_finset_1(sK1(X1,X0))
    | ~ v1_compts_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_947,plain,
    ( ~ v1_tops_2(X0,sK4)
    | ~ m1_setfam_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_finset_1(sK1(sK4,X0))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_1548,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_finset_1(sK1(sK4,X1))
    | ~ v1_compts_1(sK4)
    | sK2(sK4,X0) != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_845,c_947])).

cnf(c_1549,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_finset_1(sK1(sK4,sK2(sK4,X0)))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1548])).

cnf(c_10,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_883,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_884,plain,
    ( ~ v1_tops_2(X0,sK4)
    | ~ m1_setfam_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_1629,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_compts_1(sK4)
    | sK2(sK4,X0) != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_845,c_884])).

cnf(c_1630,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,sK2(sK4,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1629])).

cnf(c_3403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | v2_compts_1(X0,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3401,c_815,c_845,c_1276,c_1549,c_1630])).

cnf(c_3404,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_3403])).

cnf(c_4851,plain,
    ( v2_compts_1(X0_45,sK4)
    | ~ m1_setfam_1(sK2(sK4,X0_45),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0_45)),X0_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_3404])).

cnf(c_5582,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4)
    | ~ m1_setfam_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK1(sK4,sK2(sK4,u1_struct_0(sK4))),u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_compts_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4851])).

cnf(c_13,plain,
    ( v2_compts_1(X0,X1)
    | m1_setfam_1(sK2(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_829,plain,
    ( v2_compts_1(X0,X1)
    | m1_setfam_1(sK2(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_830,plain,
    ( v2_compts_1(X0,sK4)
    | m1_setfam_1(sK2(sK4,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_4857,plain,
    ( v2_compts_1(X0_45,sK4)
    | m1_setfam_1(sK2(sK4,X0_45),X0_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_830])).

cnf(c_5583,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4)
    | m1_setfam_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_4857])).

cnf(c_4858,plain,
    ( v2_compts_1(X0_45,sK4)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0_45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(subtyping,[status(esa)],[c_815])).

cnf(c_5584,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4)
    | m1_subset_1(sK2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_4858])).

cnf(c_4856,plain,
    ( v2_compts_1(X0_45,sK4)
    | v1_tops_2(sK2(sK4,X0_45),sK4)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_845])).

cnf(c_5585,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4)
    | v1_tops_2(sK2(sK4,u1_struct_0(sK4)),sK4)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_4856])).

cnf(c_4872,plain,
    ( ~ m1_subset_1(X0_45,X1_45)
    | m1_subset_1(X2_45,X3_45)
    | X2_45 != X0_45
    | X3_45 != X1_45 ),
    theory(equality)).

cnf(c_5530,plain,
    ( m1_subset_1(X0_45,X1_45)
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | X1_45 != k1_zfmisc_1(u1_struct_0(sK4))
    | X0_45 != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4872])).

cnf(c_5568,plain,
    ( m1_subset_1(u1_struct_0(sK4),X0_45)
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | X0_45 != k1_zfmisc_1(u1_struct_0(sK4))
    | u1_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5530])).

cnf(c_5581,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
    | u1_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5568])).

cnf(c_5574,plain,
    ( k2_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4869])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_312,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_0])).

cnf(c_676,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_312,c_21])).

cnf(c_677,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_4865,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_677])).

cnf(c_688,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_compts_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_689,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_19,negated_conjecture,
    ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_175,plain,
    ( ~ v1_compts_1(sK4)
    | ~ v2_compts_1(k2_struct_0(sK4),sK4) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_176,plain,
    ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | ~ v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_2114,plain,
    ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(resolution,[status(thm)],[c_689,c_176])).

cnf(c_5,plain,
    ( m1_setfam_1(sK0(X0),u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_698,plain,
    ( m1_setfam_1(sK0(X0),u1_struct_0(X0))
    | v1_compts_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_699,plain,
    ( m1_setfam_1(sK0(sK4),u1_struct_0(sK4))
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_2025,plain,
    ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | m1_setfam_1(sK0(sK4),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_699,c_176])).

cnf(c_1936,plain,
    ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | v1_tops_2(sK0(sK4),sK4) ),
    inference(resolution,[status(thm)],[c_709,c_176])).

cnf(c_1,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_77,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_74,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_20,negated_conjecture,
    ( v2_compts_1(k2_struct_0(sK4),sK4)
    | v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6154,c_6078,c_6072,c_6001,c_5896,c_5866,c_5647,c_5582,c_5583,c_5584,c_5585,c_5581,c_5574,c_4865,c_2114,c_2025,c_1936,c_77,c_74,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n015.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 15:57:23 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.18/0.32  % Running in FOF mode
% 1.82/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/0.97  
% 1.82/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.82/0.97  
% 1.82/0.97  ------  iProver source info
% 1.82/0.97  
% 1.82/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.82/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.82/0.97  git: non_committed_changes: false
% 1.82/0.97  git: last_make_outside_of_git: false
% 1.82/0.97  
% 1.82/0.97  ------ 
% 1.82/0.97  
% 1.82/0.97  ------ Input Options
% 1.82/0.97  
% 1.82/0.97  --out_options                           all
% 1.82/0.97  --tptp_safe_out                         true
% 1.82/0.97  --problem_path                          ""
% 1.82/0.97  --include_path                          ""
% 1.82/0.97  --clausifier                            res/vclausify_rel
% 1.82/0.97  --clausifier_options                    --mode clausify
% 1.82/0.97  --stdin                                 false
% 1.82/0.97  --stats_out                             all
% 1.82/0.97  
% 1.82/0.97  ------ General Options
% 1.82/0.97  
% 1.82/0.97  --fof                                   false
% 1.82/0.97  --time_out_real                         305.
% 1.82/0.97  --time_out_virtual                      -1.
% 1.82/0.97  --symbol_type_check                     false
% 1.82/0.97  --clausify_out                          false
% 1.82/0.97  --sig_cnt_out                           false
% 1.82/0.97  --trig_cnt_out                          false
% 1.82/0.97  --trig_cnt_out_tolerance                1.
% 1.82/0.97  --trig_cnt_out_sk_spl                   false
% 1.82/0.97  --abstr_cl_out                          false
% 1.82/0.97  
% 1.82/0.97  ------ Global Options
% 1.82/0.97  
% 1.82/0.97  --schedule                              default
% 1.82/0.97  --add_important_lit                     false
% 1.82/0.97  --prop_solver_per_cl                    1000
% 1.82/0.97  --min_unsat_core                        false
% 1.82/0.97  --soft_assumptions                      false
% 1.82/0.97  --soft_lemma_size                       3
% 1.82/0.97  --prop_impl_unit_size                   0
% 1.82/0.97  --prop_impl_unit                        []
% 1.82/0.97  --share_sel_clauses                     true
% 1.82/0.97  --reset_solvers                         false
% 1.82/0.97  --bc_imp_inh                            [conj_cone]
% 1.82/0.97  --conj_cone_tolerance                   3.
% 1.82/0.97  --extra_neg_conj                        none
% 1.82/0.97  --large_theory_mode                     true
% 1.82/0.97  --prolific_symb_bound                   200
% 1.82/0.97  --lt_threshold                          2000
% 1.82/0.97  --clause_weak_htbl                      true
% 1.82/0.97  --gc_record_bc_elim                     false
% 1.82/0.97  
% 1.82/0.97  ------ Preprocessing Options
% 1.82/0.97  
% 1.82/0.97  --preprocessing_flag                    true
% 1.82/0.97  --time_out_prep_mult                    0.1
% 1.82/0.97  --splitting_mode                        input
% 1.82/0.97  --splitting_grd                         true
% 1.82/0.97  --splitting_cvd                         false
% 1.82/0.97  --splitting_cvd_svl                     false
% 1.82/0.97  --splitting_nvd                         32
% 1.82/0.97  --sub_typing                            true
% 1.82/0.97  --prep_gs_sim                           true
% 1.82/0.97  --prep_unflatten                        true
% 1.82/0.97  --prep_res_sim                          true
% 1.82/0.97  --prep_upred                            true
% 1.82/0.97  --prep_sem_filter                       exhaustive
% 1.82/0.97  --prep_sem_filter_out                   false
% 1.82/0.97  --pred_elim                             true
% 1.82/0.97  --res_sim_input                         true
% 1.82/0.97  --eq_ax_congr_red                       true
% 1.82/0.97  --pure_diseq_elim                       true
% 1.82/0.97  --brand_transform                       false
% 1.82/0.97  --non_eq_to_eq                          false
% 1.82/0.97  --prep_def_merge                        true
% 1.82/0.97  --prep_def_merge_prop_impl              false
% 1.82/0.97  --prep_def_merge_mbd                    true
% 1.82/0.97  --prep_def_merge_tr_red                 false
% 1.82/0.97  --prep_def_merge_tr_cl                  false
% 1.82/0.97  --smt_preprocessing                     true
% 1.82/0.97  --smt_ac_axioms                         fast
% 1.82/0.97  --preprocessed_out                      false
% 1.82/0.97  --preprocessed_stats                    false
% 1.82/0.97  
% 1.82/0.97  ------ Abstraction refinement Options
% 1.82/0.97  
% 1.82/0.97  --abstr_ref                             []
% 1.82/0.97  --abstr_ref_prep                        false
% 1.82/0.97  --abstr_ref_until_sat                   false
% 1.82/0.97  --abstr_ref_sig_restrict                funpre
% 1.82/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.82/0.97  --abstr_ref_under                       []
% 1.82/0.97  
% 1.82/0.97  ------ SAT Options
% 1.82/0.97  
% 1.82/0.97  --sat_mode                              false
% 1.82/0.97  --sat_fm_restart_options                ""
% 1.82/0.97  --sat_gr_def                            false
% 1.82/0.97  --sat_epr_types                         true
% 1.82/0.97  --sat_non_cyclic_types                  false
% 1.82/0.97  --sat_finite_models                     false
% 1.82/0.97  --sat_fm_lemmas                         false
% 1.82/0.97  --sat_fm_prep                           false
% 1.82/0.97  --sat_fm_uc_incr                        true
% 1.82/0.97  --sat_out_model                         small
% 1.82/0.97  --sat_out_clauses                       false
% 1.82/0.97  
% 1.82/0.97  ------ QBF Options
% 1.82/0.97  
% 1.82/0.97  --qbf_mode                              false
% 1.82/0.97  --qbf_elim_univ                         false
% 1.82/0.97  --qbf_dom_inst                          none
% 1.82/0.97  --qbf_dom_pre_inst                      false
% 1.82/0.97  --qbf_sk_in                             false
% 1.82/0.97  --qbf_pred_elim                         true
% 1.82/0.97  --qbf_split                             512
% 1.82/0.97  
% 1.82/0.97  ------ BMC1 Options
% 1.82/0.97  
% 1.82/0.97  --bmc1_incremental                      false
% 1.82/0.97  --bmc1_axioms                           reachable_all
% 1.82/0.97  --bmc1_min_bound                        0
% 1.82/0.97  --bmc1_max_bound                        -1
% 1.82/0.97  --bmc1_max_bound_default                -1
% 1.82/0.97  --bmc1_symbol_reachability              true
% 1.82/0.97  --bmc1_property_lemmas                  false
% 1.82/0.97  --bmc1_k_induction                      false
% 1.82/0.97  --bmc1_non_equiv_states                 false
% 1.82/0.97  --bmc1_deadlock                         false
% 1.82/0.97  --bmc1_ucm                              false
% 1.82/0.97  --bmc1_add_unsat_core                   none
% 1.82/0.97  --bmc1_unsat_core_children              false
% 1.82/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.82/0.97  --bmc1_out_stat                         full
% 1.82/0.97  --bmc1_ground_init                      false
% 1.82/0.97  --bmc1_pre_inst_next_state              false
% 1.82/0.97  --bmc1_pre_inst_state                   false
% 1.82/0.97  --bmc1_pre_inst_reach_state             false
% 1.82/0.97  --bmc1_out_unsat_core                   false
% 1.82/0.97  --bmc1_aig_witness_out                  false
% 1.82/0.97  --bmc1_verbose                          false
% 1.82/0.97  --bmc1_dump_clauses_tptp                false
% 1.82/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.82/0.97  --bmc1_dump_file                        -
% 1.82/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.82/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.82/0.97  --bmc1_ucm_extend_mode                  1
% 1.82/0.97  --bmc1_ucm_init_mode                    2
% 1.82/0.97  --bmc1_ucm_cone_mode                    none
% 1.82/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.82/0.97  --bmc1_ucm_relax_model                  4
% 1.82/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.82/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.82/0.97  --bmc1_ucm_layered_model                none
% 1.82/0.97  --bmc1_ucm_max_lemma_size               10
% 1.82/0.97  
% 1.82/0.97  ------ AIG Options
% 1.82/0.97  
% 1.82/0.97  --aig_mode                              false
% 1.82/0.97  
% 1.82/0.97  ------ Instantiation Options
% 1.82/0.97  
% 1.82/0.97  --instantiation_flag                    true
% 1.82/0.97  --inst_sos_flag                         false
% 1.82/0.97  --inst_sos_phase                        true
% 1.82/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.82/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.82/0.97  --inst_lit_sel_side                     num_symb
% 1.82/0.97  --inst_solver_per_active                1400
% 1.82/0.97  --inst_solver_calls_frac                1.
% 1.82/0.97  --inst_passive_queue_type               priority_queues
% 1.82/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.82/0.97  --inst_passive_queues_freq              [25;2]
% 1.82/0.97  --inst_dismatching                      true
% 1.82/0.97  --inst_eager_unprocessed_to_passive     true
% 1.82/0.97  --inst_prop_sim_given                   true
% 1.82/0.97  --inst_prop_sim_new                     false
% 1.82/0.97  --inst_subs_new                         false
% 1.82/0.97  --inst_eq_res_simp                      false
% 1.82/0.97  --inst_subs_given                       false
% 1.82/0.97  --inst_orphan_elimination               true
% 1.82/0.97  --inst_learning_loop_flag               true
% 1.82/0.97  --inst_learning_start                   3000
% 1.82/0.97  --inst_learning_factor                  2
% 1.82/0.97  --inst_start_prop_sim_after_learn       3
% 1.82/0.97  --inst_sel_renew                        solver
% 1.82/0.97  --inst_lit_activity_flag                true
% 1.82/0.97  --inst_restr_to_given                   false
% 1.82/0.97  --inst_activity_threshold               500
% 1.82/0.97  --inst_out_proof                        true
% 1.82/0.97  
% 1.82/0.97  ------ Resolution Options
% 1.82/0.97  
% 1.82/0.97  --resolution_flag                       true
% 1.82/0.97  --res_lit_sel                           adaptive
% 1.82/0.97  --res_lit_sel_side                      none
% 1.82/0.97  --res_ordering                          kbo
% 1.82/0.97  --res_to_prop_solver                    active
% 1.82/0.97  --res_prop_simpl_new                    false
% 1.82/0.97  --res_prop_simpl_given                  true
% 1.82/0.97  --res_passive_queue_type                priority_queues
% 1.82/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.82/0.97  --res_passive_queues_freq               [15;5]
% 1.82/0.97  --res_forward_subs                      full
% 1.82/0.97  --res_backward_subs                     full
% 1.82/0.97  --res_forward_subs_resolution           true
% 1.82/0.97  --res_backward_subs_resolution          true
% 1.82/0.97  --res_orphan_elimination                true
% 1.82/0.97  --res_time_limit                        2.
% 1.82/0.97  --res_out_proof                         true
% 1.82/0.97  
% 1.82/0.97  ------ Superposition Options
% 1.82/0.97  
% 1.82/0.97  --superposition_flag                    true
% 1.82/0.97  --sup_passive_queue_type                priority_queues
% 1.82/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.82/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.82/0.97  --demod_completeness_check              fast
% 1.82/0.97  --demod_use_ground                      true
% 1.82/0.97  --sup_to_prop_solver                    passive
% 1.82/0.97  --sup_prop_simpl_new                    true
% 1.82/0.97  --sup_prop_simpl_given                  true
% 1.82/0.97  --sup_fun_splitting                     false
% 1.82/0.97  --sup_smt_interval                      50000
% 1.82/0.97  
% 1.82/0.97  ------ Superposition Simplification Setup
% 1.82/0.97  
% 1.82/0.97  --sup_indices_passive                   []
% 1.82/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.82/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.97  --sup_full_bw                           [BwDemod]
% 1.82/0.97  --sup_immed_triv                        [TrivRules]
% 1.82/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.82/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.97  --sup_immed_bw_main                     []
% 1.82/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.82/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.97  
% 1.82/0.97  ------ Combination Options
% 1.82/0.97  
% 1.82/0.97  --comb_res_mult                         3
% 1.82/0.97  --comb_sup_mult                         2
% 1.82/0.97  --comb_inst_mult                        10
% 1.82/0.97  
% 1.82/0.97  ------ Debug Options
% 1.82/0.97  
% 1.82/0.97  --dbg_backtrace                         false
% 1.82/0.97  --dbg_dump_prop_clauses                 false
% 1.82/0.97  --dbg_dump_prop_clauses_file            -
% 1.82/0.97  --dbg_out_stat                          false
% 1.82/0.97  ------ Parsing...
% 1.82/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.82/0.97  
% 1.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.82/0.97  
% 1.82/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.82/0.97  
% 1.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.82/0.97  ------ Proving...
% 1.82/0.97  ------ Problem Properties 
% 1.82/0.97  
% 1.82/0.97  
% 1.82/0.97  clauses                                 17
% 1.82/0.97  conjectures                             2
% 1.82/0.97  EPR                                     0
% 1.82/0.97  Horn                                    10
% 1.82/0.97  unary                                   2
% 1.82/0.97  binary                                  5
% 1.82/0.97  lits                                    59
% 1.82/0.97  lits eq                                 1
% 1.82/0.97  fd_pure                                 0
% 1.82/0.97  fd_pseudo                               0
% 1.82/0.97  fd_cond                                 0
% 1.82/0.97  fd_pseudo_cond                          0
% 1.82/0.97  AC symbols                              0
% 1.82/0.97  
% 1.82/0.97  ------ Schedule dynamic 5 is on 
% 1.82/0.97  
% 1.82/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.82/0.97  
% 1.82/0.97  
% 1.82/0.97  ------ 
% 1.82/0.97  Current options:
% 1.82/0.97  ------ 
% 1.82/0.97  
% 1.82/0.97  ------ Input Options
% 1.82/0.97  
% 1.82/0.97  --out_options                           all
% 1.82/0.97  --tptp_safe_out                         true
% 1.82/0.97  --problem_path                          ""
% 1.82/0.97  --include_path                          ""
% 1.82/0.97  --clausifier                            res/vclausify_rel
% 1.82/0.97  --clausifier_options                    --mode clausify
% 1.82/0.97  --stdin                                 false
% 1.82/0.97  --stats_out                             all
% 1.82/0.97  
% 1.82/0.97  ------ General Options
% 1.82/0.97  
% 1.82/0.97  --fof                                   false
% 1.82/0.97  --time_out_real                         305.
% 1.82/0.97  --time_out_virtual                      -1.
% 1.82/0.97  --symbol_type_check                     false
% 1.82/0.97  --clausify_out                          false
% 1.82/0.97  --sig_cnt_out                           false
% 1.82/0.97  --trig_cnt_out                          false
% 1.82/0.97  --trig_cnt_out_tolerance                1.
% 1.82/0.97  --trig_cnt_out_sk_spl                   false
% 1.82/0.97  --abstr_cl_out                          false
% 1.82/0.97  
% 1.82/0.97  ------ Global Options
% 1.82/0.97  
% 1.82/0.97  --schedule                              default
% 1.82/0.97  --add_important_lit                     false
% 1.82/0.97  --prop_solver_per_cl                    1000
% 1.82/0.97  --min_unsat_core                        false
% 1.82/0.97  --soft_assumptions                      false
% 1.82/0.97  --soft_lemma_size                       3
% 1.82/0.97  --prop_impl_unit_size                   0
% 1.82/0.97  --prop_impl_unit                        []
% 1.82/0.97  --share_sel_clauses                     true
% 1.82/0.97  --reset_solvers                         false
% 1.82/0.97  --bc_imp_inh                            [conj_cone]
% 1.82/0.97  --conj_cone_tolerance                   3.
% 1.82/0.97  --extra_neg_conj                        none
% 1.82/0.97  --large_theory_mode                     true
% 1.82/0.97  --prolific_symb_bound                   200
% 1.82/0.97  --lt_threshold                          2000
% 1.82/0.97  --clause_weak_htbl                      true
% 1.82/0.97  --gc_record_bc_elim                     false
% 1.82/0.97  
% 1.82/0.97  ------ Preprocessing Options
% 1.82/0.97  
% 1.82/0.97  --preprocessing_flag                    true
% 1.82/0.97  --time_out_prep_mult                    0.1
% 1.82/0.97  --splitting_mode                        input
% 1.82/0.97  --splitting_grd                         true
% 1.82/0.97  --splitting_cvd                         false
% 1.82/0.97  --splitting_cvd_svl                     false
% 1.82/0.97  --splitting_nvd                         32
% 1.82/0.97  --sub_typing                            true
% 1.82/0.97  --prep_gs_sim                           true
% 1.82/0.97  --prep_unflatten                        true
% 1.82/0.97  --prep_res_sim                          true
% 1.82/0.97  --prep_upred                            true
% 1.82/0.97  --prep_sem_filter                       exhaustive
% 1.82/0.97  --prep_sem_filter_out                   false
% 1.82/0.97  --pred_elim                             true
% 1.82/0.97  --res_sim_input                         true
% 1.82/0.97  --eq_ax_congr_red                       true
% 1.82/0.97  --pure_diseq_elim                       true
% 1.82/0.97  --brand_transform                       false
% 1.82/0.97  --non_eq_to_eq                          false
% 1.82/0.97  --prep_def_merge                        true
% 1.82/0.97  --prep_def_merge_prop_impl              false
% 1.82/0.97  --prep_def_merge_mbd                    true
% 1.82/0.97  --prep_def_merge_tr_red                 false
% 1.82/0.97  --prep_def_merge_tr_cl                  false
% 1.82/0.97  --smt_preprocessing                     true
% 1.82/0.97  --smt_ac_axioms                         fast
% 1.82/0.97  --preprocessed_out                      false
% 1.82/0.97  --preprocessed_stats                    false
% 1.82/0.97  
% 1.82/0.97  ------ Abstraction refinement Options
% 1.82/0.97  
% 1.82/0.97  --abstr_ref                             []
% 1.82/0.97  --abstr_ref_prep                        false
% 1.82/0.97  --abstr_ref_until_sat                   false
% 1.82/0.97  --abstr_ref_sig_restrict                funpre
% 1.82/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.82/0.97  --abstr_ref_under                       []
% 1.82/0.97  
% 1.82/0.97  ------ SAT Options
% 1.82/0.97  
% 1.82/0.97  --sat_mode                              false
% 1.82/0.97  --sat_fm_restart_options                ""
% 1.82/0.97  --sat_gr_def                            false
% 1.82/0.97  --sat_epr_types                         true
% 1.82/0.97  --sat_non_cyclic_types                  false
% 1.82/0.97  --sat_finite_models                     false
% 1.82/0.97  --sat_fm_lemmas                         false
% 1.82/0.97  --sat_fm_prep                           false
% 1.82/0.97  --sat_fm_uc_incr                        true
% 1.82/0.97  --sat_out_model                         small
% 1.82/0.97  --sat_out_clauses                       false
% 1.82/0.97  
% 1.82/0.97  ------ QBF Options
% 1.82/0.97  
% 1.82/0.97  --qbf_mode                              false
% 1.82/0.97  --qbf_elim_univ                         false
% 1.82/0.97  --qbf_dom_inst                          none
% 1.82/0.97  --qbf_dom_pre_inst                      false
% 1.82/0.97  --qbf_sk_in                             false
% 1.82/0.97  --qbf_pred_elim                         true
% 1.82/0.97  --qbf_split                             512
% 1.82/0.97  
% 1.82/0.97  ------ BMC1 Options
% 1.82/0.97  
% 1.82/0.97  --bmc1_incremental                      false
% 1.82/0.97  --bmc1_axioms                           reachable_all
% 1.82/0.97  --bmc1_min_bound                        0
% 1.82/0.97  --bmc1_max_bound                        -1
% 1.82/0.97  --bmc1_max_bound_default                -1
% 1.82/0.97  --bmc1_symbol_reachability              true
% 1.82/0.97  --bmc1_property_lemmas                  false
% 1.82/0.97  --bmc1_k_induction                      false
% 1.82/0.97  --bmc1_non_equiv_states                 false
% 1.82/0.97  --bmc1_deadlock                         false
% 1.82/0.97  --bmc1_ucm                              false
% 1.82/0.97  --bmc1_add_unsat_core                   none
% 1.82/0.97  --bmc1_unsat_core_children              false
% 1.82/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.82/0.97  --bmc1_out_stat                         full
% 1.82/0.97  --bmc1_ground_init                      false
% 1.82/0.97  --bmc1_pre_inst_next_state              false
% 1.82/0.97  --bmc1_pre_inst_state                   false
% 1.82/0.97  --bmc1_pre_inst_reach_state             false
% 1.82/0.97  --bmc1_out_unsat_core                   false
% 1.82/0.97  --bmc1_aig_witness_out                  false
% 1.82/0.97  --bmc1_verbose                          false
% 1.82/0.97  --bmc1_dump_clauses_tptp                false
% 1.82/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.82/0.97  --bmc1_dump_file                        -
% 1.82/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.82/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.82/0.97  --bmc1_ucm_extend_mode                  1
% 1.82/0.97  --bmc1_ucm_init_mode                    2
% 1.82/0.97  --bmc1_ucm_cone_mode                    none
% 1.82/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.82/0.97  --bmc1_ucm_relax_model                  4
% 1.82/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.82/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.82/0.97  --bmc1_ucm_layered_model                none
% 1.82/0.97  --bmc1_ucm_max_lemma_size               10
% 1.82/0.97  
% 1.82/0.97  ------ AIG Options
% 1.82/0.97  
% 1.82/0.97  --aig_mode                              false
% 1.82/0.97  
% 1.82/0.97  ------ Instantiation Options
% 1.82/0.97  
% 1.82/0.97  --instantiation_flag                    true
% 1.82/0.97  --inst_sos_flag                         false
% 1.82/0.97  --inst_sos_phase                        true
% 1.82/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.82/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.82/0.97  --inst_lit_sel_side                     none
% 1.82/0.97  --inst_solver_per_active                1400
% 1.82/0.97  --inst_solver_calls_frac                1.
% 1.82/0.97  --inst_passive_queue_type               priority_queues
% 1.82/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.82/0.97  --inst_passive_queues_freq              [25;2]
% 1.82/0.97  --inst_dismatching                      true
% 1.82/0.97  --inst_eager_unprocessed_to_passive     true
% 1.82/0.97  --inst_prop_sim_given                   true
% 1.82/0.97  --inst_prop_sim_new                     false
% 1.82/0.97  --inst_subs_new                         false
% 1.82/0.97  --inst_eq_res_simp                      false
% 1.82/0.97  --inst_subs_given                       false
% 1.82/0.97  --inst_orphan_elimination               true
% 1.82/0.97  --inst_learning_loop_flag               true
% 1.82/0.97  --inst_learning_start                   3000
% 1.82/0.97  --inst_learning_factor                  2
% 1.82/0.97  --inst_start_prop_sim_after_learn       3
% 1.82/0.97  --inst_sel_renew                        solver
% 1.82/0.97  --inst_lit_activity_flag                true
% 1.82/0.97  --inst_restr_to_given                   false
% 1.82/0.97  --inst_activity_threshold               500
% 1.82/0.97  --inst_out_proof                        true
% 1.82/0.97  
% 1.82/0.97  ------ Resolution Options
% 1.82/0.97  
% 1.82/0.97  --resolution_flag                       false
% 1.82/0.97  --res_lit_sel                           adaptive
% 1.82/0.97  --res_lit_sel_side                      none
% 1.82/0.97  --res_ordering                          kbo
% 1.82/0.97  --res_to_prop_solver                    active
% 1.82/0.97  --res_prop_simpl_new                    false
% 1.82/0.97  --res_prop_simpl_given                  true
% 1.82/0.97  --res_passive_queue_type                priority_queues
% 1.82/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.82/0.97  --res_passive_queues_freq               [15;5]
% 1.82/0.97  --res_forward_subs                      full
% 1.82/0.97  --res_backward_subs                     full
% 1.82/0.97  --res_forward_subs_resolution           true
% 1.82/0.97  --res_backward_subs_resolution          true
% 1.82/0.97  --res_orphan_elimination                true
% 1.82/0.97  --res_time_limit                        2.
% 1.82/0.97  --res_out_proof                         true
% 1.82/0.97  
% 1.82/0.97  ------ Superposition Options
% 1.82/0.97  
% 1.82/0.97  --superposition_flag                    true
% 1.82/0.97  --sup_passive_queue_type                priority_queues
% 1.82/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.82/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.82/0.97  --demod_completeness_check              fast
% 1.82/0.97  --demod_use_ground                      true
% 1.82/0.97  --sup_to_prop_solver                    passive
% 1.82/0.97  --sup_prop_simpl_new                    true
% 1.82/0.97  --sup_prop_simpl_given                  true
% 1.82/0.97  --sup_fun_splitting                     false
% 1.82/0.97  --sup_smt_interval                      50000
% 1.82/0.97  
% 1.82/0.97  ------ Superposition Simplification Setup
% 1.82/0.97  
% 1.82/0.97  --sup_indices_passive                   []
% 1.82/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.82/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.97  --sup_full_bw                           [BwDemod]
% 1.82/0.97  --sup_immed_triv                        [TrivRules]
% 1.82/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.82/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.97  --sup_immed_bw_main                     []
% 1.82/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.82/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.97  
% 1.82/0.97  ------ Combination Options
% 1.82/0.97  
% 1.82/0.97  --comb_res_mult                         3
% 1.82/0.97  --comb_sup_mult                         2
% 1.82/0.97  --comb_inst_mult                        10
% 1.82/0.97  
% 1.82/0.97  ------ Debug Options
% 1.82/0.97  
% 1.82/0.97  --dbg_backtrace                         false
% 1.82/0.97  --dbg_dump_prop_clauses                 false
% 1.82/0.97  --dbg_dump_prop_clauses_file            -
% 1.82/0.97  --dbg_out_stat                          false
% 1.82/0.97  
% 1.82/0.97  
% 1.82/0.97  
% 1.82/0.97  
% 1.82/0.97  ------ Proving...
% 1.82/0.97  
% 1.82/0.97  
% 1.82/0.97  % SZS status Theorem for theBenchmark.p
% 1.82/0.97  
% 1.82/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.82/0.97  
% 1.82/0.97  fof(f4,axiom,(
% 1.82/0.97    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(v1_finset_1(X2) & m1_setfam_1(X2,u1_struct_0(X0)) & r1_tarski(X2,X1))) & v1_tops_2(X1,X0) & m1_setfam_1(X1,u1_struct_0(X0))))))),
% 1.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.97  
% 1.82/0.97  fof(f11,plain,(
% 1.82/0.97    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : ((v1_finset_1(X2) & m1_setfam_1(X2,u1_struct_0(X0)) & r1_tarski(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X1,X0) | ~m1_setfam_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(ennf_transformation,[],[f4])).
% 1.82/0.97  
% 1.82/0.97  fof(f12,plain,(
% 1.82/0.97    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (v1_finset_1(X2) & m1_setfam_1(X2,u1_struct_0(X0)) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X1,X0) | ~m1_setfam_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(flattening,[],[f11])).
% 1.82/0.97  
% 1.82/0.97  fof(f16,plain,(
% 1.82/0.97    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X1,X0) & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X1] : (? [X2] : (v1_finset_1(X2) & m1_setfam_1(X2,u1_struct_0(X0)) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X1,X0) | ~m1_setfam_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(nnf_transformation,[],[f12])).
% 1.82/0.97  
% 1.82/0.97  fof(f17,plain,(
% 1.82/0.97    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X1,X0) & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X3] : (? [X4] : (v1_finset_1(X4) & m1_setfam_1(X4,u1_struct_0(X0)) & r1_tarski(X4,X3) & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(rectify,[],[f16])).
% 1.82/0.97  
% 1.82/0.97  fof(f19,plain,(
% 1.82/0.97    ! [X3,X0] : (? [X4] : (v1_finset_1(X4) & m1_setfam_1(X4,u1_struct_0(X0)) & r1_tarski(X4,X3) & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (v1_finset_1(sK1(X0,X3)) & m1_setfam_1(sK1(X0,X3),u1_struct_0(X0)) & r1_tarski(sK1(X0,X3),X3) & m1_subset_1(sK1(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.82/0.97    introduced(choice_axiom,[])).
% 1.82/0.97  
% 1.82/0.97  fof(f18,plain,(
% 1.82/0.97    ! [X0] : (? [X1] : (! [X2] : (~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X1,X0) & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (! [X2] : (~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,sK0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(sK0(X0),X0) & m1_setfam_1(sK0(X0),u1_struct_0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.82/0.97    introduced(choice_axiom,[])).
% 1.82/0.97  
% 1.82/0.97  fof(f20,plain,(
% 1.82/0.97    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,sK0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(sK0(X0),X0) & m1_setfam_1(sK0(X0),u1_struct_0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X3] : ((v1_finset_1(sK1(X0,X3)) & m1_setfam_1(sK1(X0,X3),u1_struct_0(X0)) & r1_tarski(sK1(X0,X3),X3) & m1_subset_1(sK1(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 1.82/0.97  
% 1.82/0.97  fof(f35,plain,(
% 1.82/0.97    ( ! [X0,X3] : (m1_setfam_1(sK1(X0,X3),u1_struct_0(X0)) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f20])).
% 1.82/0.97  
% 1.82/0.97  fof(f6,conjecture,(
% 1.82/0.97    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 1.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.97  
% 1.82/0.97  fof(f7,negated_conjecture,(
% 1.82/0.97    ~! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 1.82/0.97    inference(negated_conjecture,[],[f6])).
% 1.82/0.97  
% 1.82/0.97  fof(f15,plain,(
% 1.82/0.97    ? [X0] : ((v1_compts_1(X0) <~> v2_compts_1(k2_struct_0(X0),X0)) & l1_pre_topc(X0))),
% 1.82/0.97    inference(ennf_transformation,[],[f7])).
% 1.82/0.97  
% 1.82/0.97  fof(f26,plain,(
% 1.82/0.97    ? [X0] : (((~v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0)) & (v2_compts_1(k2_struct_0(X0),X0) | v1_compts_1(X0))) & l1_pre_topc(X0))),
% 1.82/0.97    inference(nnf_transformation,[],[f15])).
% 1.82/0.97  
% 1.82/0.97  fof(f27,plain,(
% 1.82/0.97    ? [X0] : ((~v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0)) & (v2_compts_1(k2_struct_0(X0),X0) | v1_compts_1(X0)) & l1_pre_topc(X0))),
% 1.82/0.97    inference(flattening,[],[f26])).
% 1.82/0.97  
% 1.82/0.97  fof(f28,plain,(
% 1.82/0.97    ? [X0] : ((~v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0)) & (v2_compts_1(k2_struct_0(X0),X0) | v1_compts_1(X0)) & l1_pre_topc(X0)) => ((~v2_compts_1(k2_struct_0(sK4),sK4) | ~v1_compts_1(sK4)) & (v2_compts_1(k2_struct_0(sK4),sK4) | v1_compts_1(sK4)) & l1_pre_topc(sK4))),
% 1.82/0.97    introduced(choice_axiom,[])).
% 1.82/0.97  
% 1.82/0.97  fof(f29,plain,(
% 1.82/0.97    (~v2_compts_1(k2_struct_0(sK4),sK4) | ~v1_compts_1(sK4)) & (v2_compts_1(k2_struct_0(sK4),sK4) | v1_compts_1(sK4)) & l1_pre_topc(sK4)),
% 1.82/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 1.82/0.97  
% 1.82/0.97  fof(f49,plain,(
% 1.82/0.97    l1_pre_topc(sK4)),
% 1.82/0.97    inference(cnf_transformation,[],[f29])).
% 1.82/0.97  
% 1.82/0.97  fof(f5,axiom,(
% 1.82/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_compts_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(v1_finset_1(X3) & m1_setfam_1(X3,X1) & r1_tarski(X3,X2))) & v1_tops_2(X2,X0) & m1_setfam_1(X2,X1))))))),
% 1.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.97  
% 1.82/0.97  fof(f13,plain,(
% 1.82/0.97    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) <=> ! [X2] : ((? [X3] : ((v1_finset_1(X3) & m1_setfam_1(X3,X1) & r1_tarski(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X2,X0) | ~m1_setfam_1(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(ennf_transformation,[],[f5])).
% 1.82/0.97  
% 1.82/0.97  fof(f14,plain,(
% 1.82/0.97    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) <=> ! [X2] : (? [X3] : (v1_finset_1(X3) & m1_setfam_1(X3,X1) & r1_tarski(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X2,X0) | ~m1_setfam_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(flattening,[],[f13])).
% 1.82/0.97  
% 1.82/0.97  fof(f21,plain,(
% 1.82/0.97    ! [X0] : (! [X1] : (((v2_compts_1(X1,X0) | ? [X2] : (! [X3] : (~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X2,X0) & m1_setfam_1(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X2] : (? [X3] : (v1_finset_1(X3) & m1_setfam_1(X3,X1) & r1_tarski(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X2,X0) | ~m1_setfam_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(nnf_transformation,[],[f14])).
% 1.82/0.97  
% 1.82/0.97  fof(f22,plain,(
% 1.82/0.97    ! [X0] : (! [X1] : (((v2_compts_1(X1,X0) | ? [X2] : (! [X3] : (~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X2,X0) & m1_setfam_1(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X4] : (? [X5] : (v1_finset_1(X5) & m1_setfam_1(X5,X1) & r1_tarski(X5,X4) & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(rectify,[],[f21])).
% 1.82/0.97  
% 1.82/0.97  fof(f24,plain,(
% 1.82/0.97    ! [X4,X1,X0] : (? [X5] : (v1_finset_1(X5) & m1_setfam_1(X5,X1) & r1_tarski(X5,X4) & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (v1_finset_1(sK3(X0,X1,X4)) & m1_setfam_1(sK3(X0,X1,X4),X1) & r1_tarski(sK3(X0,X1,X4),X4) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.82/0.97    introduced(choice_axiom,[])).
% 1.82/0.97  
% 1.82/0.97  fof(f23,plain,(
% 1.82/0.97    ! [X1,X0] : (? [X2] : (! [X3] : (~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(X2,X0) & m1_setfam_1(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (! [X3] : (~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,sK2(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(sK2(X0,X1),X0) & m1_setfam_1(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.82/0.97    introduced(choice_axiom,[])).
% 1.82/0.97  
% 1.82/0.97  fof(f25,plain,(
% 1.82/0.97    ! [X0] : (! [X1] : (((v2_compts_1(X1,X0) | (! [X3] : (~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,sK2(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & v1_tops_2(sK2(X0,X1),X0) & m1_setfam_1(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X4] : ((v1_finset_1(sK3(X0,X1,X4)) & m1_setfam_1(sK3(X0,X1,X4),X1) & r1_tarski(sK3(X0,X1,X4),X4) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f24,f23])).
% 1.82/0.97  
% 1.82/0.97  fof(f43,plain,(
% 1.82/0.97    ( ! [X4,X0,X1] : (m1_setfam_1(sK3(X0,X1,X4),X1) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f25])).
% 1.82/0.97  
% 1.82/0.97  fof(f42,plain,(
% 1.82/0.97    ( ! [X4,X0,X1] : (r1_tarski(sK3(X0,X1,X4),X4) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f25])).
% 1.82/0.97  
% 1.82/0.97  fof(f40,plain,(
% 1.82/0.97    ( ! [X2,X0] : (v1_compts_1(X0) | ~v1_finset_1(X2) | ~m1_setfam_1(X2,u1_struct_0(X0)) | ~r1_tarski(X2,sK0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f20])).
% 1.82/0.97  
% 1.82/0.97  fof(f37,plain,(
% 1.82/0.97    ( ! [X0] : (v1_compts_1(X0) | m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f20])).
% 1.82/0.97  
% 1.82/0.97  fof(f39,plain,(
% 1.82/0.97    ( ! [X0] : (v1_compts_1(X0) | v1_tops_2(sK0(X0),X0) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f20])).
% 1.82/0.97  
% 1.82/0.97  fof(f44,plain,(
% 1.82/0.97    ( ! [X4,X0,X1] : (v1_finset_1(sK3(X0,X1,X4)) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f25])).
% 1.82/0.97  
% 1.82/0.97  fof(f41,plain,(
% 1.82/0.97    ( ! [X4,X0,X1] : (m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X4,X0) | ~m1_setfam_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f25])).
% 1.82/0.97  
% 1.82/0.97  fof(f48,plain,(
% 1.82/0.97    ( ! [X0,X3,X1] : (v2_compts_1(X1,X0) | ~v1_finset_1(X3) | ~m1_setfam_1(X3,X1) | ~r1_tarski(X3,sK2(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f25])).
% 1.82/0.97  
% 1.82/0.97  fof(f34,plain,(
% 1.82/0.97    ( ! [X0,X3] : (r1_tarski(sK1(X0,X3),X3) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f20])).
% 1.82/0.97  
% 1.82/0.97  fof(f45,plain,(
% 1.82/0.97    ( ! [X0,X1] : (v2_compts_1(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f25])).
% 1.82/0.97  
% 1.82/0.97  fof(f47,plain,(
% 1.82/0.97    ( ! [X0,X1] : (v2_compts_1(X1,X0) | v1_tops_2(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f25])).
% 1.82/0.97  
% 1.82/0.97  fof(f36,plain,(
% 1.82/0.97    ( ! [X0,X3] : (v1_finset_1(sK1(X0,X3)) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f20])).
% 1.82/0.97  
% 1.82/0.97  fof(f33,plain,(
% 1.82/0.97    ( ! [X0,X3] : (m1_subset_1(sK1(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X3,X0) | ~m1_setfam_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f20])).
% 1.82/0.97  
% 1.82/0.97  fof(f46,plain,(
% 1.82/0.97    ( ! [X0,X1] : (v2_compts_1(X1,X0) | m1_setfam_1(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f25])).
% 1.82/0.97  
% 1.82/0.97  fof(f3,axiom,(
% 1.82/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.97  
% 1.82/0.97  fof(f10,plain,(
% 1.82/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.82/0.97    inference(ennf_transformation,[],[f3])).
% 1.82/0.97  
% 1.82/0.97  fof(f32,plain,(
% 1.82/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f10])).
% 1.82/0.97  
% 1.82/0.97  fof(f1,axiom,(
% 1.82/0.97    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.97  
% 1.82/0.97  fof(f8,plain,(
% 1.82/0.97    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.82/0.97    inference(ennf_transformation,[],[f1])).
% 1.82/0.97  
% 1.82/0.97  fof(f30,plain,(
% 1.82/0.97    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f8])).
% 1.82/0.97  
% 1.82/0.97  fof(f51,plain,(
% 1.82/0.97    ~v2_compts_1(k2_struct_0(sK4),sK4) | ~v1_compts_1(sK4)),
% 1.82/0.97    inference(cnf_transformation,[],[f29])).
% 1.82/0.97  
% 1.82/0.97  fof(f38,plain,(
% 1.82/0.97    ( ! [X0] : (v1_compts_1(X0) | m1_setfam_1(sK0(X0),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f20])).
% 1.82/0.97  
% 1.82/0.97  fof(f2,axiom,(
% 1.82/0.97    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.97  
% 1.82/0.97  fof(f9,plain,(
% 1.82/0.97    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.82/0.97    inference(ennf_transformation,[],[f2])).
% 1.82/0.97  
% 1.82/0.97  fof(f31,plain,(
% 1.82/0.97    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.82/0.97    inference(cnf_transformation,[],[f9])).
% 1.82/0.97  
% 1.82/0.97  fof(f50,plain,(
% 1.82/0.97    v2_compts_1(k2_struct_0(sK4),sK4) | v1_compts_1(sK4)),
% 1.82/0.97    inference(cnf_transformation,[],[f29])).
% 1.82/0.97  
% 1.82/0.97  cnf(c_8,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,X1)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(X1))
% 1.82/0.97      | m1_setfam_1(sK1(X1,X0),u1_struct_0(X1))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ v1_compts_1(X1)
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f35]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_21,negated_conjecture,
% 1.82/0.97      ( l1_pre_topc(sK4) ),
% 1.82/0.97      inference(cnf_transformation,[],[f49]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_925,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,X1)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(X1))
% 1.82/0.97      | m1_setfam_1(sK1(X1,X0),u1_struct_0(X1))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ v1_compts_1(X1)
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_926,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(sK4))
% 1.82/0.97      | m1_setfam_1(sK1(sK4,X0),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_925]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4854,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0_45,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X0_45,u1_struct_0(sK4))
% 1.82/0.97      | m1_setfam_1(sK1(sK4,X0_45),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(subtyping,[status(esa)],[c_926]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_6154,plain,
% 1.82/0.97      ( ~ v1_tops_2(sK2(sK4,u1_struct_0(sK4)),sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.82/0.97      | m1_setfam_1(sK1(sK4,sK2(sK4,u1_struct_0(sK4))),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(sK2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4854]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4876,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0_45,X0_46)
% 1.82/0.97      | v2_compts_1(X1_45,X0_46)
% 1.82/0.97      | X1_45 != X0_45 ),
% 1.82/0.97      theory(equality) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5782,plain,
% 1.82/0.97      ( v2_compts_1(X0_45,sK4)
% 1.82/0.97      | ~ v2_compts_1(k2_struct_0(sK4),sK4)
% 1.82/0.97      | X0_45 != k2_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4876]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_6078,plain,
% 1.82/0.97      ( v2_compts_1(u1_struct_0(sK4),sK4)
% 1.82/0.97      | ~ v2_compts_1(k2_struct_0(sK4),sK4)
% 1.82/0.97      | u1_struct_0(sK4) != k2_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_5782]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_16,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,X1)
% 1.82/0.97      | ~ v1_tops_2(X2,X1)
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | m1_setfam_1(sK3(X1,X0,X2),X0)
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f43]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_766,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,X1)
% 1.82/0.97      | ~ v1_tops_2(X2,X1)
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | m1_setfam_1(sK3(X1,X0,X2),X0)
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_767,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(X1,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X1,X0)
% 1.82/0.97      | m1_setfam_1(sK3(sK4,X0,X1),X0)
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_766]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4859,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0_45,sK4)
% 1.82/0.97      | ~ v1_tops_2(X1_45,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X1_45,X0_45)
% 1.82/0.97      | m1_setfam_1(sK3(sK4,X0_45,X1_45),X0_45)
% 1.82/0.97      | ~ m1_subset_1(X1_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(subtyping,[status(esa)],[c_767]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5651,plain,
% 1.82/0.97      ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
% 1.82/0.97      | ~ v1_tops_2(X0_45,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X0_45,u1_struct_0(sK4))
% 1.82/0.97      | m1_setfam_1(sK3(sK4,u1_struct_0(sK4),X0_45),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4859]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_6072,plain,
% 1.82/0.97      ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
% 1.82/0.97      | ~ v1_tops_2(sK0(sK4),sK4)
% 1.82/0.97      | m1_setfam_1(sK3(sK4,u1_struct_0(sK4),sK0(sK4)),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_5651]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5665,plain,
% 1.82/0.97      ( v2_compts_1(X0_45,sK4)
% 1.82/0.97      | ~ v2_compts_1(u1_struct_0(sK4),sK4)
% 1.82/0.97      | X0_45 != u1_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4876]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_6001,plain,
% 1.82/0.97      ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
% 1.82/0.97      | v2_compts_1(k2_struct_0(sK4),sK4)
% 1.82/0.97      | k2_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_5665]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4870,plain,
% 1.82/0.97      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.82/0.97      theory(equality) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5645,plain,
% 1.82/0.97      ( X0_45 != X1_45
% 1.82/0.97      | k2_struct_0(sK4) != X1_45
% 1.82/0.97      | k2_struct_0(sK4) = X0_45 ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4870]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5731,plain,
% 1.82/0.97      ( X0_45 != k2_struct_0(sK4)
% 1.82/0.97      | k2_struct_0(sK4) = X0_45
% 1.82/0.97      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_5645]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5896,plain,
% 1.82/0.97      ( u1_struct_0(sK4) != k2_struct_0(sK4)
% 1.82/0.97      | k2_struct_0(sK4) = u1_struct_0(sK4)
% 1.82/0.97      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_5731]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_17,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,X1)
% 1.82/0.97      | ~ v1_tops_2(X2,X1)
% 1.82/0.97      | r1_tarski(sK3(X1,X0,X2),X2)
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f42]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_742,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,X1)
% 1.82/0.97      | ~ v1_tops_2(X2,X1)
% 1.82/0.97      | r1_tarski(sK3(X1,X0,X2),X2)
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_743,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(X1,sK4)
% 1.82/0.97      | r1_tarski(sK3(sK4,X0,X1),X1)
% 1.82/0.97      | ~ m1_setfam_1(X1,X0)
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_742]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_3,plain,
% 1.82/0.97      ( ~ r1_tarski(X0,sK0(X1))
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(X1))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ v1_finset_1(X0)
% 1.82/0.97      | v1_compts_1(X1)
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f40]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_967,plain,
% 1.82/0.97      ( ~ r1_tarski(X0,sK0(X1))
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(X1))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ v1_finset_1(X0)
% 1.82/0.97      | v1_compts_1(X1)
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_968,plain,
% 1.82/0.97      ( ~ r1_tarski(X0,sK0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_finset_1(X0)
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_967]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_3375,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(X1,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X1,X0)
% 1.82/0.97      | ~ m1_setfam_1(X2,u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ v1_finset_1(X2)
% 1.82/0.97      | v1_compts_1(sK4)
% 1.82/0.97      | sK3(sK4,X0,X1) != X2
% 1.82/0.97      | sK0(sK4) != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_743,c_968]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_3376,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(sK0(sK4),sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_finset_1(sK3(sK4,X0,sK0(sK4)))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_3375]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_6,plain,
% 1.82/0.97      ( m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 1.82/0.97      | v1_compts_1(X0)
% 1.82/0.97      | ~ l1_pre_topc(X0) ),
% 1.82/0.97      inference(cnf_transformation,[],[f37]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_62,plain,
% 1.82/0.97      ( m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | v1_compts_1(sK4)
% 1.82/0.97      | ~ l1_pre_topc(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4,plain,
% 1.82/0.97      ( v1_tops_2(sK0(X0),X0) | v1_compts_1(X0) | ~ l1_pre_topc(X0) ),
% 1.82/0.97      inference(cnf_transformation,[],[f39]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_68,plain,
% 1.82/0.97      ( v1_tops_2(sK0(sK4),sK4) | v1_compts_1(sK4) | ~ l1_pre_topc(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1242,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(X1,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X1,X0)
% 1.82/0.97      | ~ m1_setfam_1(X2,u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ v1_finset_1(X2)
% 1.82/0.97      | v1_compts_1(sK4)
% 1.82/0.97      | sK3(sK4,X0,X1) != X2
% 1.82/0.97      | sK0(sK4) != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_743,c_968]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1243,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(sK0(sK4),sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_finset_1(sK3(sK4,X0,sK0(sK4)))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_1242]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_708,plain,
% 1.82/0.97      ( v1_tops_2(sK0(X0),X0) | v1_compts_1(X0) | sK4 != X0 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_709,plain,
% 1.82/0.97      ( v1_tops_2(sK0(sK4),sK4) | v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_708]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_15,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,X1)
% 1.82/0.97      | ~ v1_tops_2(X2,X1)
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | v1_finset_1(sK3(X1,X0,X2))
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f44]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_790,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,X1)
% 1.82/0.97      | ~ v1_tops_2(X2,X1)
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | v1_finset_1(sK3(X1,X0,X2))
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_791,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(X1,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X1,X0)
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | v1_finset_1(sK3(sK4,X0,X1)) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_790]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1332,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X1,X0)
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | v1_finset_1(sK3(sK4,X0,X1))
% 1.82/0.97      | v1_compts_1(sK4)
% 1.82/0.97      | sK0(sK4) != X1
% 1.82/0.97      | sK4 != sK4 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_709,c_791]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1333,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | v1_finset_1(sK3(sK4,X0,sK0(sK4)))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_1332]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1337,plain,
% 1.82/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0)
% 1.82/0.97      | ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | v1_finset_1(sK3(sK4,X0,sK0(sK4)))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(global_propositional_subsumption,
% 1.82/0.97                [status(thm)],
% 1.82/0.97                [c_1333,c_21,c_62]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1338,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | v1_finset_1(sK3(sK4,X0,sK0(sK4)))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(renaming,[status(thm)],[c_1337]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_18,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,X1)
% 1.82/0.97      | ~ v1_tops_2(X2,X1)
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f41]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_718,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,X1)
% 1.82/0.97      | ~ v1_tops_2(X2,X1)
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_719,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(X1,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X1,X0)
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_718]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1413,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X1,X0)
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | v1_compts_1(sK4)
% 1.82/0.97      | sK0(sK4) != X1
% 1.82/0.97      | sK4 != sK4 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_709,c_719]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1414,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_1413]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1418,plain,
% 1.82/0.97      ( m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0)
% 1.82/0.97      | ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(global_propositional_subsumption,
% 1.82/0.97                [status(thm)],
% 1.82/0.97                [c_1414,c_21,c_62]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1419,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(renaming,[status(thm)],[c_1418]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_3378,plain,
% 1.82/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0)
% 1.82/0.97      | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
% 1.82/0.97      | ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(global_propositional_subsumption,
% 1.82/0.97                [status(thm)],
% 1.82/0.97                [c_3376,c_21,c_62,c_68,c_1243,c_1338,c_1419]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_3379,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(renaming,[status(thm)],[c_3378]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4852,plain,
% 1.82/0.97      ( ~ v2_compts_1(X0_45,sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK3(sK4,X0_45,sK0(sK4)),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),X0_45)
% 1.82/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(subtyping,[status(esa)],[c_3379]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5866,plain,
% 1.82/0.97      ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK3(sK4,u1_struct_0(sK4),sK0(sK4)),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK0(sK4),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4852]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4869,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5647,plain,
% 1.82/0.97      ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4869]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_11,plain,
% 1.82/0.97      ( v2_compts_1(X0,X1)
% 1.82/0.97      | ~ r1_tarski(X2,sK2(X1,X0))
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | ~ v1_finset_1(X2)
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f48]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_859,plain,
% 1.82/0.97      ( v2_compts_1(X0,X1)
% 1.82/0.97      | ~ r1_tarski(X2,sK2(X1,X0))
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | ~ v1_finset_1(X2)
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_860,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ r1_tarski(X1,sK2(sK4,X0))
% 1.82/0.97      | ~ m1_setfam_1(X1,X0)
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ v1_finset_1(X1) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_859]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_9,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,X1)
% 1.82/0.97      | r1_tarski(sK1(X1,X0),X0)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(X1))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ v1_compts_1(X1)
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f34]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_904,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,X1)
% 1.82/0.97      | r1_tarski(sK1(X1,X0),X0)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(X1))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ v1_compts_1(X1)
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_905,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,sK4)
% 1.82/0.97      | r1_tarski(sK1(sK4,X0),X0)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_904]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_3400,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(X1,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | ~ m1_setfam_1(X1,u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ v1_finset_1(X2)
% 1.82/0.97      | ~ v1_compts_1(sK4)
% 1.82/0.97      | sK2(sK4,X0) != X1
% 1.82/0.97      | sK1(sK4,X1) != X2 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_860,c_905]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_3401,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(sK2(sK4,X0),sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(sK1(sK4,sK2(sK4,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_finset_1(sK1(sK4,sK2(sK4,X0)))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_3400]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_14,plain,
% 1.82/0.97      ( v2_compts_1(X0,X1)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f45]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_814,plain,
% 1.82/0.97      ( v2_compts_1(X0,X1)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_815,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_814]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_12,plain,
% 1.82/0.97      ( v2_compts_1(X0,X1)
% 1.82/0.97      | v1_tops_2(sK2(X1,X0),X1)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f47]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_844,plain,
% 1.82/0.97      ( v2_compts_1(X0,X1)
% 1.82/0.97      | v1_tops_2(sK2(X1,X0),X1)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_845,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | v1_tops_2(sK2(sK4,X0),sK4)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_844]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1275,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(X1,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X2,X0)
% 1.82/0.97      | ~ m1_setfam_1(X1,u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ v1_finset_1(X2)
% 1.82/0.97      | ~ v1_compts_1(sK4)
% 1.82/0.97      | sK2(sK4,X0) != X1
% 1.82/0.97      | sK1(sK4,X1) != X2 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_860,c_905]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1276,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_tops_2(sK2(sK4,X0),sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(sK1(sK4,sK2(sK4,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_finset_1(sK1(sK4,sK2(sK4,X0)))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_1275]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_7,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,X1)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(X1))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | v1_finset_1(sK1(X1,X0))
% 1.82/0.97      | ~ v1_compts_1(X1)
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f36]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_946,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,X1)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(X1))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | v1_finset_1(sK1(X1,X0))
% 1.82/0.97      | ~ v1_compts_1(X1)
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_947,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | v1_finset_1(sK1(sK4,X0))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_946]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1548,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X1,u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | v1_finset_1(sK1(sK4,X1))
% 1.82/0.97      | ~ v1_compts_1(sK4)
% 1.82/0.97      | sK2(sK4,X0) != X1
% 1.82/0.97      | sK4 != sK4 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_845,c_947]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1549,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | v1_finset_1(sK1(sK4,sK2(sK4,X0)))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_1548]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_10,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,X1)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(X1))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ v1_compts_1(X1)
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f33]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_883,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,X1)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(X1))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.82/0.97      | ~ v1_compts_1(X1)
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_884,plain,
% 1.82/0.97      ( ~ v1_tops_2(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X0,u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_883]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1629,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(X1,u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | m1_subset_1(sK1(sK4,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_compts_1(sK4)
% 1.82/0.97      | sK2(sK4,X0) != X1
% 1.82/0.97      | sK4 != sK4 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_845,c_884]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1630,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | m1_subset_1(sK1(sK4,sK2(sK4,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_1629]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_3403,plain,
% 1.82/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
% 1.82/0.97      | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
% 1.82/0.97      | v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(global_propositional_subsumption,
% 1.82/0.97                [status(thm)],
% 1.82/0.97                [c_3401,c_815,c_845,c_1276,c_1549,c_1630]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_3404,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(renaming,[status(thm)],[c_3403]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4851,plain,
% 1.82/0.97      ( v2_compts_1(X0_45,sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK2(sK4,X0_45),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0_45)),X0_45)
% 1.82/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(subtyping,[status(esa)],[c_3404]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5582,plain,
% 1.82/0.97      ( v2_compts_1(u1_struct_0(sK4),sK4)
% 1.82/0.97      | ~ m1_setfam_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_setfam_1(sK1(sK4,sK2(sK4,u1_struct_0(sK4))),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4851]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_13,plain,
% 1.82/0.97      ( v2_compts_1(X0,X1)
% 1.82/0.97      | m1_setfam_1(sK2(X1,X0),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | ~ l1_pre_topc(X1) ),
% 1.82/0.97      inference(cnf_transformation,[],[f46]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_829,plain,
% 1.82/0.97      ( v2_compts_1(X0,X1)
% 1.82/0.97      | m1_setfam_1(sK2(X1,X0),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/0.97      | sK4 != X1 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_830,plain,
% 1.82/0.97      ( v2_compts_1(X0,sK4)
% 1.82/0.97      | m1_setfam_1(sK2(sK4,X0),X0)
% 1.82/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_829]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4857,plain,
% 1.82/0.97      ( v2_compts_1(X0_45,sK4)
% 1.82/0.97      | m1_setfam_1(sK2(sK4,X0_45),X0_45)
% 1.82/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(subtyping,[status(esa)],[c_830]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5583,plain,
% 1.82/0.97      ( v2_compts_1(u1_struct_0(sK4),sK4)
% 1.82/0.97      | m1_setfam_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.82/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4857]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4858,plain,
% 1.82/0.97      ( v2_compts_1(X0_45,sK4)
% 1.82/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | m1_subset_1(sK2(sK4,X0_45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 1.82/0.97      inference(subtyping,[status(esa)],[c_815]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5584,plain,
% 1.82/0.97      ( v2_compts_1(u1_struct_0(sK4),sK4)
% 1.82/0.97      | m1_subset_1(sK2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4858]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4856,plain,
% 1.82/0.97      ( v2_compts_1(X0_45,sK4)
% 1.82/0.97      | v1_tops_2(sK2(sK4,X0_45),sK4)
% 1.82/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(subtyping,[status(esa)],[c_845]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5585,plain,
% 1.82/0.97      ( v2_compts_1(u1_struct_0(sK4),sK4)
% 1.82/0.97      | v1_tops_2(sK2(sK4,u1_struct_0(sK4)),sK4)
% 1.82/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4856]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4872,plain,
% 1.82/0.97      ( ~ m1_subset_1(X0_45,X1_45)
% 1.82/0.97      | m1_subset_1(X2_45,X3_45)
% 1.82/0.97      | X2_45 != X0_45
% 1.82/0.97      | X3_45 != X1_45 ),
% 1.82/0.97      theory(equality) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5530,plain,
% 1.82/0.97      ( m1_subset_1(X0_45,X1_45)
% 1.82/0.97      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | X1_45 != k1_zfmisc_1(u1_struct_0(sK4))
% 1.82/0.97      | X0_45 != k2_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4872]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5568,plain,
% 1.82/0.97      ( m1_subset_1(u1_struct_0(sK4),X0_45)
% 1.82/0.97      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | X0_45 != k1_zfmisc_1(u1_struct_0(sK4))
% 1.82/0.97      | u1_struct_0(sK4) != k2_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_5530]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5581,plain,
% 1.82/0.97      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
% 1.82/0.97      | u1_struct_0(sK4) != k2_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_5568]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5574,plain,
% 1.82/0.97      ( k2_struct_0(sK4) = k2_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_4869]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_2,plain,
% 1.82/0.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.82/0.97      inference(cnf_transformation,[],[f32]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_0,plain,
% 1.82/0.97      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.82/0.97      inference(cnf_transformation,[],[f30]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_312,plain,
% 1.82/0.97      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.82/0.97      inference(resolution,[status(thm)],[c_2,c_0]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_676,plain,
% 1.82/0.97      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_312,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_677,plain,
% 1.82/0.97      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_676]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_4865,plain,
% 1.82/0.97      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 1.82/0.97      inference(subtyping,[status(esa)],[c_677]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_688,plain,
% 1.82/0.97      ( m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 1.82/0.97      | v1_compts_1(X0)
% 1.82/0.97      | sK4 != X0 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_689,plain,
% 1.82/0.97      ( m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.82/0.97      | v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_688]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_19,negated_conjecture,
% 1.82/0.97      ( ~ v2_compts_1(k2_struct_0(sK4),sK4) | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(cnf_transformation,[],[f51]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_175,plain,
% 1.82/0.97      ( ~ v1_compts_1(sK4) | ~ v2_compts_1(k2_struct_0(sK4),sK4) ),
% 1.82/0.97      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_176,plain,
% 1.82/0.97      ( ~ v2_compts_1(k2_struct_0(sK4),sK4) | ~ v1_compts_1(sK4) ),
% 1.82/0.97      inference(renaming,[status(thm)],[c_175]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_2114,plain,
% 1.82/0.97      ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
% 1.82/0.97      | m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 1.82/0.97      inference(resolution,[status(thm)],[c_689,c_176]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_5,plain,
% 1.82/0.97      ( m1_setfam_1(sK0(X0),u1_struct_0(X0))
% 1.82/0.97      | v1_compts_1(X0)
% 1.82/0.97      | ~ l1_pre_topc(X0) ),
% 1.82/0.97      inference(cnf_transformation,[],[f38]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_698,plain,
% 1.82/0.97      ( m1_setfam_1(sK0(X0),u1_struct_0(X0))
% 1.82/0.97      | v1_compts_1(X0)
% 1.82/0.97      | sK4 != X0 ),
% 1.82/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_699,plain,
% 1.82/0.97      ( m1_setfam_1(sK0(sK4),u1_struct_0(sK4)) | v1_compts_1(sK4) ),
% 1.82/0.97      inference(unflattening,[status(thm)],[c_698]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_2025,plain,
% 1.82/0.97      ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
% 1.82/0.97      | m1_setfam_1(sK0(sK4),u1_struct_0(sK4)) ),
% 1.82/0.97      inference(resolution,[status(thm)],[c_699,c_176]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1936,plain,
% 1.82/0.97      ( ~ v2_compts_1(k2_struct_0(sK4),sK4) | v1_tops_2(sK0(sK4),sK4) ),
% 1.82/0.97      inference(resolution,[status(thm)],[c_709,c_176]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_1,plain,
% 1.82/0.97      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.82/0.97      | ~ l1_struct_0(X0) ),
% 1.82/0.97      inference(cnf_transformation,[],[f31]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_77,plain,
% 1.82/0.97      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.82/0.97      | ~ l1_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_74,plain,
% 1.82/0.97      ( ~ l1_pre_topc(sK4) | l1_struct_0(sK4) ),
% 1.82/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(c_20,negated_conjecture,
% 1.82/0.97      ( v2_compts_1(k2_struct_0(sK4),sK4) | v1_compts_1(sK4) ),
% 1.82/0.97      inference(cnf_transformation,[],[f50]) ).
% 1.82/0.97  
% 1.82/0.97  cnf(contradiction,plain,
% 1.82/0.97      ( $false ),
% 1.82/0.97      inference(minisat,
% 1.82/0.97                [status(thm)],
% 1.82/0.97                [c_6154,c_6078,c_6072,c_6001,c_5896,c_5866,c_5647,c_5582,
% 1.82/0.97                 c_5583,c_5584,c_5585,c_5581,c_5574,c_4865,c_2114,c_2025,
% 1.82/0.97                 c_1936,c_77,c_74,c_19,c_20,c_21]) ).
% 1.82/0.97  
% 1.82/0.97  
% 1.82/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.82/0.97  
% 1.82/0.97  ------                               Statistics
% 1.82/0.97  
% 1.82/0.97  ------ General
% 1.82/0.97  
% 1.82/0.97  abstr_ref_over_cycles:                  0
% 1.82/0.97  abstr_ref_under_cycles:                 0
% 1.82/0.97  gc_basic_clause_elim:                   0
% 1.82/0.97  forced_gc_time:                         0
% 1.82/0.97  parsing_time:                           0.011
% 1.82/0.97  unif_index_cands_time:                  0.
% 1.82/0.97  unif_index_add_time:                    0.
% 1.82/0.97  orderings_time:                         0.
% 1.82/0.97  out_proof_time:                         0.011
% 1.82/0.97  total_time:                             0.159
% 1.82/0.97  num_of_symbols:                         47
% 1.82/0.97  num_of_terms:                           2732
% 1.82/0.97  
% 1.82/0.97  ------ Preprocessing
% 1.82/0.97  
% 1.82/0.97  num_of_splits:                          0
% 1.82/0.97  num_of_split_atoms:                     0
% 1.82/0.97  num_of_reused_defs:                     0
% 1.82/0.97  num_eq_ax_congr_red:                    28
% 1.82/0.97  num_of_sem_filtered_clauses:            1
% 1.82/0.97  num_of_subtypes:                        2
% 1.82/0.97  monotx_restored_types:                  0
% 1.82/0.97  sat_num_of_epr_types:                   0
% 1.82/0.97  sat_num_of_non_cyclic_types:            0
% 1.82/0.97  sat_guarded_non_collapsed_types:        0
% 1.82/0.97  num_pure_diseq_elim:                    0
% 1.82/0.97  simp_replaced_by:                       0
% 1.82/0.97  res_preprocessed:                       112
% 1.82/0.97  prep_upred:                             0
% 1.82/0.97  prep_unflattend:                        94
% 1.82/0.97  smt_new_axioms:                         0
% 1.82/0.97  pred_elim_cands:                        5
% 1.82/0.97  pred_elim:                              4
% 1.82/0.97  pred_elim_cl:                           5
% 1.82/0.97  pred_elim_cycles:                       16
% 1.82/0.97  merged_defs:                            10
% 1.82/0.97  merged_defs_ncl:                        0
% 1.82/0.97  bin_hyper_res:                          10
% 1.82/0.97  prep_cycles:                            5
% 1.82/0.97  pred_elim_time:                         0.074
% 1.82/0.97  splitting_time:                         0.
% 1.82/0.97  sem_filter_time:                        0.
% 1.82/0.97  monotx_time:                            0.
% 1.82/0.97  subtype_inf_time:                       0.
% 1.82/0.97  
% 1.82/0.97  ------ Problem properties
% 1.82/0.97  
% 1.82/0.97  clauses:                                17
% 1.82/0.97  conjectures:                            2
% 1.82/0.97  epr:                                    0
% 1.82/0.97  horn:                                   10
% 1.82/0.97  ground:                                 7
% 1.82/0.97  unary:                                  2
% 1.82/0.97  binary:                                 5
% 1.82/0.97  lits:                                   59
% 1.82/0.97  lits_eq:                                1
% 1.82/0.97  fd_pure:                                0
% 1.82/0.97  fd_pseudo:                              0
% 1.82/0.97  fd_cond:                                0
% 1.82/0.97  fd_pseudo_cond:                         0
% 1.82/0.97  ac_symbols:                             0
% 1.82/0.97  
% 1.82/0.97  ------ Propositional Solver
% 1.82/0.97  
% 1.82/0.97  prop_solver_calls:                      32
% 1.82/0.97  prop_fast_solver_calls:                 1990
% 1.82/0.97  smt_solver_calls:                       0
% 1.82/0.97  smt_fast_solver_calls:                  0
% 1.82/0.97  prop_num_of_clauses:                    929
% 1.82/0.97  prop_preprocess_simplified:             3878
% 1.82/0.97  prop_fo_subsumed:                       51
% 1.82/0.97  prop_solver_time:                       0.
% 1.82/0.97  smt_solver_time:                        0.
% 1.82/0.97  smt_fast_solver_time:                   0.
% 1.82/0.97  prop_fast_solver_time:                  0.
% 1.82/0.97  prop_unsat_core_time:                   0.
% 1.82/0.97  
% 1.82/0.97  ------ QBF
% 1.82/0.97  
% 1.82/0.97  qbf_q_res:                              0
% 1.82/0.97  qbf_num_tautologies:                    0
% 1.82/0.97  qbf_prep_cycles:                        0
% 1.82/0.97  
% 1.82/0.97  ------ BMC1
% 1.82/0.97  
% 1.82/0.97  bmc1_current_bound:                     -1
% 1.82/0.97  bmc1_last_solved_bound:                 -1
% 1.82/0.97  bmc1_unsat_core_size:                   -1
% 1.82/0.97  bmc1_unsat_core_parents_size:           -1
% 1.82/0.97  bmc1_merge_next_fun:                    0
% 1.82/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.82/0.97  
% 1.82/0.97  ------ Instantiation
% 1.82/0.97  
% 1.82/0.97  inst_num_of_clauses:                    114
% 1.82/0.97  inst_num_in_passive:                    30
% 1.82/0.97  inst_num_in_active:                     79
% 1.82/0.97  inst_num_in_unprocessed:                4
% 1.82/0.97  inst_num_of_loops:                      107
% 1.82/0.97  inst_num_of_learning_restarts:          0
% 1.82/0.97  inst_num_moves_active_passive:          22
% 1.82/0.97  inst_lit_activity:                      0
% 1.82/0.97  inst_lit_activity_moves:                0
% 1.82/0.97  inst_num_tautologies:                   0
% 1.82/0.97  inst_num_prop_implied:                  0
% 1.82/0.97  inst_num_existing_simplified:           0
% 1.82/0.97  inst_num_eq_res_simplified:             0
% 1.82/0.97  inst_num_child_elim:                    0
% 1.82/0.97  inst_num_of_dismatching_blockings:      3
% 1.82/0.97  inst_num_of_non_proper_insts:           93
% 1.82/0.97  inst_num_of_duplicates:                 0
% 1.82/0.97  inst_inst_num_from_inst_to_res:         0
% 1.82/0.97  inst_dismatching_checking_time:         0.
% 1.82/0.97  
% 1.82/0.97  ------ Resolution
% 1.82/0.97  
% 1.82/0.97  res_num_of_clauses:                     0
% 1.82/0.97  res_num_in_passive:                     0
% 1.82/0.97  res_num_in_active:                      0
% 1.82/0.97  res_num_of_loops:                       117
% 1.82/0.97  res_forward_subset_subsumed:            8
% 1.82/0.97  res_backward_subset_subsumed:           0
% 1.82/0.97  res_forward_subsumed:                   0
% 1.82/0.97  res_backward_subsumed:                  0
% 1.82/0.97  res_forward_subsumption_resolution:     12
% 1.82/0.97  res_backward_subsumption_resolution:    0
% 1.82/0.97  res_clause_to_clause_subsumption:       205
% 1.82/0.97  res_orphan_elimination:                 0
% 1.82/0.97  res_tautology_del:                      55
% 1.82/0.97  res_num_eq_res_simplified:              0
% 1.82/0.97  res_num_sel_changes:                    0
% 1.82/0.97  res_moves_from_active_to_pass:          0
% 1.82/0.97  
% 1.82/0.97  ------ Superposition
% 1.82/0.97  
% 1.82/0.97  sup_time_total:                         0.
% 1.82/0.97  sup_time_generating:                    0.
% 1.82/0.97  sup_time_sim_full:                      0.
% 1.82/0.97  sup_time_sim_immed:                     0.
% 1.82/0.97  
% 1.82/0.97  sup_num_of_clauses:                     27
% 1.82/0.97  sup_num_in_active:                      20
% 1.82/0.97  sup_num_in_passive:                     7
% 1.82/0.97  sup_num_of_loops:                       20
% 1.82/0.97  sup_fw_superposition:                   4
% 1.82/0.97  sup_bw_superposition:                   7
% 1.82/0.97  sup_immediate_simplified:               1
% 1.82/0.97  sup_given_eliminated:                   0
% 1.82/0.97  comparisons_done:                       0
% 1.82/0.97  comparisons_avoided:                    0
% 1.82/0.97  
% 1.82/0.97  ------ Simplifications
% 1.82/0.97  
% 1.82/0.97  
% 1.82/0.97  sim_fw_subset_subsumed:                 1
% 1.82/0.97  sim_bw_subset_subsumed:                 0
% 1.82/0.97  sim_fw_subsumed:                        0
% 1.82/0.97  sim_bw_subsumed:                        0
% 1.82/0.97  sim_fw_subsumption_res:                 0
% 1.82/0.97  sim_bw_subsumption_res:                 0
% 1.82/0.97  sim_tautology_del:                      1
% 1.82/0.97  sim_eq_tautology_del:                   0
% 1.82/0.97  sim_eq_res_simp:                        0
% 1.82/0.97  sim_fw_demodulated:                     0
% 1.82/0.97  sim_bw_demodulated:                     0
% 1.82/0.97  sim_light_normalised:                   13
% 1.82/0.97  sim_joinable_taut:                      0
% 1.82/0.97  sim_joinable_simp:                      0
% 1.82/0.97  sim_ac_normalised:                      0
% 1.82/0.97  sim_smt_subsumption:                    0
% 1.82/0.97  
%------------------------------------------------------------------------------
