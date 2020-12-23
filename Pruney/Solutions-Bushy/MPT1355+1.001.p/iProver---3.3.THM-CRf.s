%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1355+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:33 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  181 (1735 expanded)
%              Number of clauses        :  130 ( 469 expanded)
%              Number of leaves         :   11 ( 372 expanded)
%              Depth                    :   22
%              Number of atoms          :  940 (11342 expanded)
%              Number of equality atoms :  136 ( 345 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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
    inference(nnf_transformation,[],[f12])).

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
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(nnf_transformation,[],[f9])).

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

fof(f32,plain,(
    ! [X0,X3] :
      ( m1_setfam_1(sK1(X0,X3),u1_struct_0(X0))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | v1_tops_2(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( m1_setfam_1(sK3(X0,X1,X4),X1)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | m1_setfam_1(sK0(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v1_tops_2(sK0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,
    ( v2_compts_1(k2_struct_0(sK4),sK4)
    | v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X4),X4)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ v1_finset_1(X2)
      | ~ m1_setfam_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X2,sK0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( v1_finset_1(sK3(X0,X1,X4))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v1_finset_1(X3)
      | ~ m1_setfam_1(X3,X1)
      | ~ r1_tarski(X3,sK2(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X0,X3] :
      ( r1_tarski(sK1(X0,X3),X3)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0,X3] :
      ( v1_finset_1(sK1(X0,X3))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK1(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | m1_setfam_1(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,
    ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_814,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_815,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_4858,plain,
    ( v2_compts_1(X0_45,sK4)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0_45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(subtyping,[status(esa)],[c_815])).

cnf(c_5314,plain,
    ( v2_compts_1(X0_45,sK4) = iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK4,X0_45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4858])).

cnf(c_5,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | m1_setfam_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_compts_1(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_925,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | m1_setfam_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_926,plain,
    ( ~ v1_tops_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(X0,u1_struct_0(sK4))
    | m1_setfam_1(sK1(sK4,X0),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_925])).

cnf(c_4854,plain,
    ( ~ v1_tops_2(X0_45,sK4)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(X0_45,u1_struct_0(sK4))
    | m1_setfam_1(sK1(sK4,X0_45),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_926])).

cnf(c_5318,plain,
    ( v1_tops_2(X0_45,sK4) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | m1_setfam_1(X0_45,u1_struct_0(sK4)) != iProver_top
    | m1_setfam_1(sK1(sK4,X0_45),u1_struct_0(sK4)) = iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4854])).

cnf(c_5838,plain,
    ( v2_compts_1(X0_45,sK4) = iProver_top
    | v1_tops_2(sK2(sK4,X0_45),sK4) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_setfam_1(sK2(sK4,X0_45),u1_struct_0(sK4)) != iProver_top
    | m1_setfam_1(sK1(sK4,sK2(sK4,X0_45)),u1_struct_0(sK4)) = iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5314,c_5318])).

cnf(c_10,plain,
    ( v2_compts_1(X0,X1)
    | v1_tops_2(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_844,plain,
    ( v2_compts_1(X0,X1)
    | v1_tops_2(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_845,plain,
    ( v2_compts_1(X0,sK4)
    | v1_tops_2(sK2(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_4856,plain,
    ( v2_compts_1(X0_45,sK4)
    | v1_tops_2(sK2(sK4,X0_45),sK4)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_845])).

cnf(c_4905,plain,
    ( v2_compts_1(X0_45,sK4) = iProver_top
    | v1_tops_2(sK2(sK4,X0_45),sK4) = iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4856])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_688,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_compts_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_689,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_4863,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_689])).

cnf(c_5309,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4863])).

cnf(c_14,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_setfam_1(X2,X0)
    | m1_setfam_1(sK3(X1,X0,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_766,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_setfam_1(X2,X0)
    | m1_setfam_1(sK3(X1,X0,X2),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_767,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(X1,X0)
    | m1_setfam_1(sK3(sK4,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_4859,plain,
    ( ~ v2_compts_1(X0_45,sK4)
    | ~ v1_tops_2(X1_45,sK4)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(X1_45,X0_45)
    | m1_setfam_1(sK3(sK4,X0_45,X1_45),X0_45) ),
    inference(subtyping,[status(esa)],[c_767])).

cnf(c_5313,plain,
    ( v2_compts_1(X0_45,sK4) != iProver_top
    | v1_tops_2(X1_45,sK4) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_setfam_1(X1_45,X0_45) != iProver_top
    | m1_setfam_1(sK3(sK4,X0_45,X1_45),X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4859])).

cnf(c_5692,plain,
    ( v2_compts_1(X0_45,sK4) != iProver_top
    | v1_tops_2(sK0(sK4),sK4) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_setfam_1(sK3(sK4,X0_45,sK0(sK4)),X0_45) = iProver_top
    | m1_setfam_1(sK0(sK4),X0_45) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5309,c_5313])).

cnf(c_22,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_70,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_compts_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_72,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_2,plain,
    ( m1_setfam_1(sK0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_73,plain,
    ( m1_setfam_1(sK0(X0),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_compts_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_75,plain,
    ( m1_setfam_1(sK0(sK4),u1_struct_0(sK4)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_1,plain,
    ( v1_tops_2(sK0(X0),X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_76,plain,
    ( v1_tops_2(sK0(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_compts_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_78,plain,
    ( v1_tops_2(sK0(sK4),sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_18,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_301,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_18,c_17])).

cnf(c_681,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_301,c_21])).

cnf(c_682,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_4864,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_682])).

cnf(c_5308,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4864])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_312,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_18,c_8])).

cnf(c_676,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_312,c_21])).

cnf(c_677,plain,
    ( k2_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_4865,plain,
    ( k2_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_677])).

cnf(c_5324,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5308,c_4865])).

cnf(c_20,negated_conjecture,
    ( v2_compts_1(k2_struct_0(sK4),sK4)
    | v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4866,negated_conjecture,
    ( v2_compts_1(k2_struct_0(sK4),sK4)
    | v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_5307,plain,
    ( v2_compts_1(k2_struct_0(sK4),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4866])).

cnf(c_5327,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5307,c_4865])).

cnf(c_15,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK3(X1,X0,X2),X2)
    | ~ m1_setfam_1(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_742,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK3(X1,X0,X2),X2)
    | ~ m1_setfam_1(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_743,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK3(sK4,X0,X1),X1)
    | ~ m1_setfam_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,sK0(X1))
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_finset_1(X0)
    | v1_compts_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_967,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,sK0(X1))
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ v1_finset_1(X0)
    | v1_compts_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_968,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r1_tarski(X0,sK0(sK4))
    | ~ m1_setfam_1(X0,u1_struct_0(sK4))
    | ~ v1_finset_1(X0)
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_967])).

cnf(c_3375,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(X1,X0)
    | ~ m1_setfam_1(X2,u1_struct_0(sK4))
    | ~ v1_finset_1(X2)
    | v1_compts_1(sK4)
    | sK3(sK4,X0,X1) != X2
    | sK0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_743,c_968])).

cnf(c_3376,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(sK0(sK4),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ v1_finset_1(sK3(sK4,X0,sK0(sK4)))
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_3375])).

cnf(c_71,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4)
    | v1_compts_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_77,plain,
    ( v1_tops_2(sK0(sK4),sK4)
    | ~ l1_pre_topc(sK4)
    | v1_compts_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1242,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(X1,X0)
    | ~ m1_setfam_1(X2,u1_struct_0(sK4))
    | ~ v1_finset_1(X2)
    | v1_compts_1(sK4)
    | sK3(sK4,X0,X1) != X2
    | sK0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_743,c_968])).

cnf(c_1243,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(sK0(sK4),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | ~ v1_finset_1(sK3(sK4,X0,sK0(sK4)))
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1242])).

cnf(c_708,plain,
    ( v1_tops_2(sK0(X0),X0)
    | v1_compts_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_709,plain,
    ( v1_tops_2(sK0(sK4),sK4)
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_13,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_setfam_1(X2,X0)
    | ~ l1_pre_topc(X1)
    | v1_finset_1(sK3(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_790,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_setfam_1(X2,X0)
    | v1_finset_1(sK3(X1,X0,X2))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_791,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(X1,X0)
    | v1_finset_1(sK3(sK4,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_790])).

cnf(c_1332,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(X1,X0)
    | v1_finset_1(sK3(sK4,X0,X1))
    | v1_compts_1(sK4)
    | sK0(sK4) != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_709,c_791])).

cnf(c_1333,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | v1_finset_1(sK3(sK4,X0,sK0(sK4)))
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1332])).

cnf(c_1337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(sK0(sK4),X0)
    | v1_finset_1(sK3(sK4,X0,sK0(sK4)))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1333,c_21,c_71])).

cnf(c_1338,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | v1_finset_1(sK3(sK4,X0,sK0(sK4)))
    | v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_1337])).

cnf(c_16,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_718,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_719,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_1413,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(X1,X0)
    | v1_compts_1(sK4)
    | sK0(sK4) != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_709,c_719])).

cnf(c_1414,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1413])).

cnf(c_1418,plain,
    ( m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_compts_1(X0,sK4)
    | ~ m1_setfam_1(sK0(sK4),X0)
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1414,c_21,c_71])).

cnf(c_1419,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,sK0(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_1418])).

cnf(c_3378,plain,
    ( ~ m1_setfam_1(sK0(sK4),X0)
    | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_compts_1(X0,sK4)
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3376,c_21,c_71,c_77,c_1243,c_1338,c_1419])).

cnf(c_3379,plain,
    ( ~ v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(sK3(sK4,X0,sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),X0)
    | v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_3378])).

cnf(c_4852,plain,
    ( ~ v2_compts_1(X0_45,sK4)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(sK3(sK4,X0_45,sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),X0_45)
    | v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_3379])).

cnf(c_6048,plain,
    ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(sK3(sK4,u1_struct_0(sK4),sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),u1_struct_0(sK4))
    | v1_compts_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4852])).

cnf(c_6049,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_setfam_1(sK3(sK4,u1_struct_0(sK4),sK0(sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_setfam_1(sK0(sK4),u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6048])).

cnf(c_5894,plain,
    ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
    | ~ v1_tops_2(X0_45,sK4)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(X0_45,u1_struct_0(sK4))
    | m1_setfam_1(sK3(sK4,u1_struct_0(sK4),X0_45),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4859])).

cnf(c_6108,plain,
    ( ~ v2_compts_1(u1_struct_0(sK4),sK4)
    | ~ v1_tops_2(sK0(sK4),sK4)
    | ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_setfam_1(sK3(sK4,u1_struct_0(sK4),sK0(sK4)),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5894])).

cnf(c_6109,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4) != iProver_top
    | v1_tops_2(sK0(sK4),sK4) != iProver_top
    | m1_subset_1(sK0(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_setfam_1(sK3(sK4,u1_struct_0(sK4),sK0(sK4)),u1_struct_0(sK4)) = iProver_top
    | m1_setfam_1(sK0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6108])).

cnf(c_6225,plain,
    ( v1_compts_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5692,c_22,c_72,c_75,c_78,c_5324,c_5327,c_6049,c_6109])).

cnf(c_6285,plain,
    ( m1_setfam_1(sK1(sK4,sK2(sK4,X0_45)),u1_struct_0(sK4)) = iProver_top
    | m1_setfam_1(sK2(sK4,X0_45),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_compts_1(X0_45,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5838,c_22,c_72,c_75,c_78,c_4905,c_5324,c_5327,c_6049,c_6109])).

cnf(c_6286,plain,
    ( v2_compts_1(X0_45,sK4) = iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_setfam_1(sK2(sK4,X0_45),u1_struct_0(sK4)) != iProver_top
    | m1_setfam_1(sK1(sK4,sK2(sK4,X0_45)),u1_struct_0(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6285])).

cnf(c_9,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,sK2(X1,X0))
    | ~ m1_setfam_1(X2,X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_finset_1(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_859,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,sK2(X1,X0))
    | ~ m1_setfam_1(X2,X0)
    | ~ v1_finset_1(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_860,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,sK2(sK4,X0))
    | ~ m1_setfam_1(X1,X0)
    | ~ v1_finset_1(X1) ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_6,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_compts_1(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_904,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_905,plain,
    ( ~ v1_tops_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r1_tarski(sK1(sK4,X0),X0)
    | ~ m1_setfam_1(X0,u1_struct_0(sK4))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_3400,plain,
    ( v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_setfam_1(X1,u1_struct_0(sK4))
    | ~ v1_finset_1(X2)
    | ~ v1_compts_1(sK4)
    | sK2(sK4,X0) != X1
    | sK1(sK4,X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_860,c_905])).

cnf(c_3401,plain,
    ( v2_compts_1(X0,sK4)
    | ~ v1_tops_2(sK2(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK1(sK4,sK2(sK4,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
    | ~ v1_finset_1(sK1(sK4,sK2(sK4,X0)))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_3400])).

cnf(c_1275,plain,
    ( v2_compts_1(X0,sK4)
    | ~ v1_tops_2(X1,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(X2,X0)
    | ~ m1_setfam_1(X1,u1_struct_0(sK4))
    | ~ v1_finset_1(X2)
    | ~ v1_compts_1(sK4)
    | sK2(sK4,X0) != X1
    | sK1(sK4,X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_860,c_905])).

cnf(c_1276,plain,
    ( v2_compts_1(X0,sK4)
    | ~ v1_tops_2(sK2(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK1(sK4,sK2(sK4,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
    | ~ v1_finset_1(sK1(sK4,sK2(sK4,X0)))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1275])).

cnf(c_4,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v1_finset_1(sK1(X1,X0))
    | ~ v1_compts_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_946,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | v1_finset_1(sK1(X1,X0))
    | ~ v1_compts_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_947,plain,
    ( ~ v1_tops_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(X0,u1_struct_0(sK4))
    | v1_finset_1(sK1(sK4,X0))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_1548,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(X1,u1_struct_0(sK4))
    | v1_finset_1(sK1(sK4,X1))
    | ~ v1_compts_1(sK4)
    | sK2(sK4,X0) != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_845,c_947])).

cnf(c_1549,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | v1_finset_1(sK1(sK4,sK2(sK4,X0)))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1548])).

cnf(c_7,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_compts_1(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_883,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X0,u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_884,plain,
    ( ~ v1_tops_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(X0,u1_struct_0(sK4))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_1629,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(X1,u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | sK2(sK4,X0) != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_845,c_884])).

cnf(c_1630,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,sK2(sK4,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1629])).

cnf(c_3403,plain,
    ( ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_compts_1(X0,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3401,c_815,c_845,c_1276,c_1549,c_1630])).

cnf(c_3404,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0)),X0)
    | ~ v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_3403])).

cnf(c_4851,plain,
    ( v2_compts_1(X0_45,sK4)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_setfam_1(sK2(sK4,X0_45),u1_struct_0(sK4))
    | ~ m1_setfam_1(sK1(sK4,sK2(sK4,X0_45)),X0_45)
    | ~ v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_3404])).

cnf(c_5321,plain,
    ( v2_compts_1(X0_45,sK4) = iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_setfam_1(sK2(sK4,X0_45),u1_struct_0(sK4)) != iProver_top
    | m1_setfam_1(sK1(sK4,sK2(sK4,X0_45)),X0_45) != iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4851])).

cnf(c_6295,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_setfam_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6286,c_5321])).

cnf(c_11,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_setfam_1(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_829,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_setfam_1(sK2(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_830,plain,
    ( v2_compts_1(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_setfam_1(sK2(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_4857,plain,
    ( v2_compts_1(X0_45,sK4)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_setfam_1(sK2(sK4,X0_45),X0_45) ),
    inference(subtyping,[status(esa)],[c_830])).

cnf(c_5315,plain,
    ( v2_compts_1(X0_45,sK4) = iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_setfam_1(sK2(sK4,X0_45),X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4857])).

cnf(c_5761,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4) = iProver_top
    | m1_setfam_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5324,c_5315])).

cnf(c_19,negated_conjecture,
    ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4867,negated_conjecture,
    ( ~ v2_compts_1(k2_struct_0(sK4),sK4)
    | ~ v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_5306,plain,
    ( v2_compts_1(k2_struct_0(sK4),sK4) != iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4867])).

cnf(c_5340,plain,
    ( v2_compts_1(u1_struct_0(sK4),sK4) != iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5306,c_4865])).

cnf(c_6219,plain,
    ( m1_setfam_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5761,c_22,c_72,c_75,c_78,c_5324,c_5340,c_5327,c_6049,c_6109])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6295,c_6225,c_6219,c_5340,c_5324])).


%------------------------------------------------------------------------------
