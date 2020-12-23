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
% DateTime   : Thu Dec  3 12:18:25 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 913 expanded)
%              Number of clauses        :  103 ( 179 expanded)
%              Number of leaves         :   17 ( 264 expanded)
%              Depth                    :   21
%              Number of atoms          :  964 (9850 expanded)
%              Number of equality atoms :   57 ( 119 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,X0,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f50,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK5(X4),X1)
        & m1_connsp_2(sK5(X4),X0,X4)
        & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK4)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK4,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,X0,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,sK3)
                  | ~ m1_connsp_2(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,sK3)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_pre_topc(sK3,X0) )
        & ( ! [X4] :
              ( ? [X5] :
                  ( r1_tarski(X5,sK3)
                  & m1_connsp_2(X5,X0,X4)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,sK3)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | v3_pre_topc(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,sK2,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK2)) )
            | ~ v3_pre_topc(X1,sK2) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,sK2,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            | v3_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ( ! [X3] :
            ( ~ r1_tarski(X3,sK3)
            | ~ m1_connsp_2(X3,sK2,sK4)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & r2_hidden(sK4,sK3)
        & m1_subset_1(sK4,u1_struct_0(sK2)) )
      | ~ v3_pre_topc(sK3,sK2) )
    & ( ! [X4] :
          ( ( r1_tarski(sK5(X4),sK3)
            & m1_connsp_2(sK5(X4),sK2,X4)
            & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2))) )
          | ~ r2_hidden(X4,sK3)
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      | v3_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f46,f50,f49,f48,f47])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK1(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK1(X0,X1,X2))
                    & r1_tarski(sK1(X0,X1,X2),X2)
                    & v3_pre_topc(sK1(X0,X1,X2),X0)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    ! [X4] :
      ( m1_connsp_2(sK5(X4),sK2,X4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ! [X4] :
      ( r1_tarski(sK5(X4),sK3)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | ~ m1_connsp_2(X3,sK2,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_212,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_15])).

cnf(c_213,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_440,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_213,c_31])).

cnf(c_441,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_445,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_30,c_29])).

cnf(c_23469,plain,
    ( ~ m1_connsp_2(sK3,sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
    | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5097,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK3)
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_11125,plain,
    ( ~ r1_tarski(X0,sK5(sK0(sK3,k1_tops_1(sK2,sK3))))
    | r1_tarski(X0,sK3)
    | ~ r1_tarski(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_5097])).

cnf(c_16736,plain,
    ( ~ r1_tarski(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK5(sK0(sK3,k1_tops_1(sK2,sK3))))
    | r1_tarski(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK3)
    | ~ r1_tarski(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_11125])).

cnf(c_17,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_545,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_31])).

cnf(c_546,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X2,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_550,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X2,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_30,c_29])).

cnf(c_551,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X2,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X0) ),
    inference(renaming,[status(thm)],[c_550])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_570,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X2,sK2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_551,c_9])).

cnf(c_7790,plain,
    ( m1_connsp_2(X0,sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
    | ~ v3_pre_topc(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))))
    | ~ r1_tarski(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),X0) ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_15324,plain,
    ( m1_connsp_2(sK3,sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
    | ~ v3_pre_topc(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK2)
    | ~ m1_subset_1(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))))
    | ~ r1_tarski(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK3) ),
    inference(instantiation,[status(thm)],[c_7790])).

cnf(c_19,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_195,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_15])).

cnf(c_196,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_482,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_196,c_31])).

cnf(c_483,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_tarski(sK1(sK2,X1,X0),X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_487,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_tarski(sK1(sK2,X1,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_30,c_29])).

cnf(c_7129,plain,
    ( ~ m1_connsp_2(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
    | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | r1_tarski(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_18,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_15])).

cnf(c_203,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_461,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_203,c_31])).

cnf(c_462,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK1(sK2,X1,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_466,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK1(sK2,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_30,c_29])).

cnf(c_7126,plain,
    ( ~ m1_connsp_2(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
    | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3))))) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_21,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_15])).

cnf(c_182,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_181])).

cnf(c_524,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_182,c_31])).

cnf(c_525,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_529,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_30,c_29])).

cnf(c_7123,plain,
    ( ~ m1_connsp_2(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
    | m1_subset_1(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_20,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_188,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_15])).

cnf(c_189,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_503,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_189,c_31])).

cnf(c_504,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | v3_pre_topc(sK1(sK2,X1,X0),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_508,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | v3_pre_topc(sK1(sK2,X1,X0),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_30,c_29])).

cnf(c_7068,plain,
    ( ~ m1_connsp_2(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
    | v3_pre_topc(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK2)
    | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_5682,plain,
    ( m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6548,plain,
    ( m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_5682])).

cnf(c_26,negated_conjecture,
    ( m1_connsp_2(sK5(X0),sK2,X0)
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_5690,plain,
    ( m1_connsp_2(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3)
    | r1_tarski(sK5(X0),sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5692,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK3)
    | r1_tarski(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4465,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK2,sK4)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4471,plain,
    ( m1_connsp_2(X0,sK2,sK4) != iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4744,plain,
    ( m1_connsp_2(sK3,sK2,sK4) != iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4465,c_4471])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_46,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5092,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5095,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5092])).

cnf(c_16,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_580,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_581,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_585,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_581,c_30,c_29])).

cnf(c_601,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_585,c_9])).

cnf(c_5115,plain,
    ( m1_connsp_2(sK3,sK2,sK4)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_5116,plain,
    ( m1_connsp_2(sK3,sK2,sK4) = iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5115])).

cnf(c_5203,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4744,c_35,c_46,c_5095,c_5116])).

cnf(c_5205,plain,
    ( ~ v3_pre_topc(sK3,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5203])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4835,plain,
    ( r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK3)
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4836,plain,
    ( ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4786,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_695,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_30])).

cnf(c_696,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_700,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_696,c_29])).

cnf(c_701,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_700])).

cnf(c_787,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_701])).

cnf(c_788,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_3760,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_788])).

cnf(c_3761,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_788])).

cnf(c_3759,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_788])).

cnf(c_3865,plain,
    ( k1_tops_1(sK2,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3760,c_3761,c_3759])).

cnf(c_3866,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_3865])).

cnf(c_4728,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_3866])).

cnf(c_4729,plain,
    ( k1_tops_1(sK2,sK3) != sK3
    | v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4728])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_4725,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23469,c_16736,c_15324,c_7129,c_7126,c_7123,c_7068,c_6548,c_5690,c_5692,c_5205,c_5203,c_4835,c_4836,c_4786,c_4729,c_4725,c_35,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.11/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/1.50  
% 7.11/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.11/1.50  
% 7.11/1.50  ------  iProver source info
% 7.11/1.50  
% 7.11/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.11/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.11/1.50  git: non_committed_changes: false
% 7.11/1.50  git: last_make_outside_of_git: false
% 7.11/1.50  
% 7.11/1.50  ------ 
% 7.11/1.50  
% 7.11/1.50  ------ Input Options
% 7.11/1.50  
% 7.11/1.50  --out_options                           all
% 7.11/1.50  --tptp_safe_out                         true
% 7.11/1.50  --problem_path                          ""
% 7.11/1.50  --include_path                          ""
% 7.11/1.50  --clausifier                            res/vclausify_rel
% 7.11/1.50  --clausifier_options                    --mode clausify
% 7.11/1.50  --stdin                                 false
% 7.11/1.50  --stats_out                             all
% 7.11/1.50  
% 7.11/1.50  ------ General Options
% 7.11/1.50  
% 7.11/1.50  --fof                                   false
% 7.11/1.50  --time_out_real                         305.
% 7.11/1.50  --time_out_virtual                      -1.
% 7.11/1.50  --symbol_type_check                     false
% 7.11/1.50  --clausify_out                          false
% 7.11/1.50  --sig_cnt_out                           false
% 7.11/1.50  --trig_cnt_out                          false
% 7.11/1.50  --trig_cnt_out_tolerance                1.
% 7.11/1.50  --trig_cnt_out_sk_spl                   false
% 7.11/1.50  --abstr_cl_out                          false
% 7.11/1.50  
% 7.11/1.50  ------ Global Options
% 7.11/1.50  
% 7.11/1.50  --schedule                              default
% 7.11/1.50  --add_important_lit                     false
% 7.11/1.50  --prop_solver_per_cl                    1000
% 7.11/1.50  --min_unsat_core                        false
% 7.11/1.50  --soft_assumptions                      false
% 7.11/1.50  --soft_lemma_size                       3
% 7.11/1.50  --prop_impl_unit_size                   0
% 7.11/1.50  --prop_impl_unit                        []
% 7.11/1.50  --share_sel_clauses                     true
% 7.11/1.50  --reset_solvers                         false
% 7.11/1.50  --bc_imp_inh                            [conj_cone]
% 7.11/1.50  --conj_cone_tolerance                   3.
% 7.11/1.50  --extra_neg_conj                        none
% 7.11/1.50  --large_theory_mode                     true
% 7.11/1.50  --prolific_symb_bound                   200
% 7.11/1.50  --lt_threshold                          2000
% 7.11/1.50  --clause_weak_htbl                      true
% 7.11/1.50  --gc_record_bc_elim                     false
% 7.11/1.50  
% 7.11/1.50  ------ Preprocessing Options
% 7.11/1.50  
% 7.11/1.50  --preprocessing_flag                    true
% 7.11/1.50  --time_out_prep_mult                    0.1
% 7.11/1.50  --splitting_mode                        input
% 7.11/1.50  --splitting_grd                         true
% 7.11/1.50  --splitting_cvd                         false
% 7.11/1.50  --splitting_cvd_svl                     false
% 7.11/1.50  --splitting_nvd                         32
% 7.11/1.50  --sub_typing                            true
% 7.11/1.50  --prep_gs_sim                           true
% 7.11/1.50  --prep_unflatten                        true
% 7.11/1.50  --prep_res_sim                          true
% 7.11/1.50  --prep_upred                            true
% 7.11/1.50  --prep_sem_filter                       exhaustive
% 7.11/1.50  --prep_sem_filter_out                   false
% 7.11/1.50  --pred_elim                             true
% 7.11/1.50  --res_sim_input                         true
% 7.11/1.50  --eq_ax_congr_red                       true
% 7.11/1.50  --pure_diseq_elim                       true
% 7.11/1.50  --brand_transform                       false
% 7.11/1.50  --non_eq_to_eq                          false
% 7.11/1.50  --prep_def_merge                        true
% 7.11/1.50  --prep_def_merge_prop_impl              false
% 7.11/1.50  --prep_def_merge_mbd                    true
% 7.11/1.50  --prep_def_merge_tr_red                 false
% 7.11/1.50  --prep_def_merge_tr_cl                  false
% 7.11/1.50  --smt_preprocessing                     true
% 7.11/1.50  --smt_ac_axioms                         fast
% 7.11/1.50  --preprocessed_out                      false
% 7.11/1.50  --preprocessed_stats                    false
% 7.11/1.50  
% 7.11/1.50  ------ Abstraction refinement Options
% 7.11/1.50  
% 7.11/1.50  --abstr_ref                             []
% 7.11/1.50  --abstr_ref_prep                        false
% 7.11/1.50  --abstr_ref_until_sat                   false
% 7.11/1.50  --abstr_ref_sig_restrict                funpre
% 7.11/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.11/1.50  --abstr_ref_under                       []
% 7.11/1.50  
% 7.11/1.50  ------ SAT Options
% 7.11/1.50  
% 7.11/1.50  --sat_mode                              false
% 7.11/1.50  --sat_fm_restart_options                ""
% 7.11/1.50  --sat_gr_def                            false
% 7.11/1.50  --sat_epr_types                         true
% 7.11/1.50  --sat_non_cyclic_types                  false
% 7.11/1.50  --sat_finite_models                     false
% 7.11/1.50  --sat_fm_lemmas                         false
% 7.11/1.50  --sat_fm_prep                           false
% 7.11/1.50  --sat_fm_uc_incr                        true
% 7.11/1.50  --sat_out_model                         small
% 7.11/1.50  --sat_out_clauses                       false
% 7.11/1.50  
% 7.11/1.50  ------ QBF Options
% 7.11/1.50  
% 7.11/1.50  --qbf_mode                              false
% 7.11/1.50  --qbf_elim_univ                         false
% 7.11/1.50  --qbf_dom_inst                          none
% 7.11/1.50  --qbf_dom_pre_inst                      false
% 7.11/1.50  --qbf_sk_in                             false
% 7.11/1.50  --qbf_pred_elim                         true
% 7.11/1.50  --qbf_split                             512
% 7.11/1.50  
% 7.11/1.50  ------ BMC1 Options
% 7.11/1.50  
% 7.11/1.50  --bmc1_incremental                      false
% 7.11/1.50  --bmc1_axioms                           reachable_all
% 7.11/1.50  --bmc1_min_bound                        0
% 7.11/1.50  --bmc1_max_bound                        -1
% 7.11/1.50  --bmc1_max_bound_default                -1
% 7.11/1.50  --bmc1_symbol_reachability              true
% 7.11/1.50  --bmc1_property_lemmas                  false
% 7.11/1.50  --bmc1_k_induction                      false
% 7.11/1.50  --bmc1_non_equiv_states                 false
% 7.11/1.50  --bmc1_deadlock                         false
% 7.11/1.50  --bmc1_ucm                              false
% 7.11/1.50  --bmc1_add_unsat_core                   none
% 7.11/1.50  --bmc1_unsat_core_children              false
% 7.11/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.11/1.50  --bmc1_out_stat                         full
% 7.11/1.50  --bmc1_ground_init                      false
% 7.11/1.50  --bmc1_pre_inst_next_state              false
% 7.11/1.50  --bmc1_pre_inst_state                   false
% 7.11/1.50  --bmc1_pre_inst_reach_state             false
% 7.11/1.50  --bmc1_out_unsat_core                   false
% 7.11/1.50  --bmc1_aig_witness_out                  false
% 7.11/1.50  --bmc1_verbose                          false
% 7.11/1.50  --bmc1_dump_clauses_tptp                false
% 7.11/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.11/1.50  --bmc1_dump_file                        -
% 7.11/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.11/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.11/1.50  --bmc1_ucm_extend_mode                  1
% 7.11/1.50  --bmc1_ucm_init_mode                    2
% 7.11/1.50  --bmc1_ucm_cone_mode                    none
% 7.11/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.11/1.50  --bmc1_ucm_relax_model                  4
% 7.11/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.11/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.11/1.50  --bmc1_ucm_layered_model                none
% 7.11/1.50  --bmc1_ucm_max_lemma_size               10
% 7.11/1.50  
% 7.11/1.50  ------ AIG Options
% 7.11/1.50  
% 7.11/1.50  --aig_mode                              false
% 7.11/1.50  
% 7.11/1.50  ------ Instantiation Options
% 7.11/1.50  
% 7.11/1.50  --instantiation_flag                    true
% 7.11/1.50  --inst_sos_flag                         false
% 7.11/1.50  --inst_sos_phase                        true
% 7.11/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.11/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.11/1.50  --inst_lit_sel_side                     num_symb
% 7.11/1.50  --inst_solver_per_active                1400
% 7.11/1.50  --inst_solver_calls_frac                1.
% 7.11/1.50  --inst_passive_queue_type               priority_queues
% 7.11/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.11/1.50  --inst_passive_queues_freq              [25;2]
% 7.11/1.50  --inst_dismatching                      true
% 7.11/1.50  --inst_eager_unprocessed_to_passive     true
% 7.11/1.50  --inst_prop_sim_given                   true
% 7.11/1.50  --inst_prop_sim_new                     false
% 7.11/1.50  --inst_subs_new                         false
% 7.11/1.50  --inst_eq_res_simp                      false
% 7.11/1.50  --inst_subs_given                       false
% 7.11/1.50  --inst_orphan_elimination               true
% 7.11/1.50  --inst_learning_loop_flag               true
% 7.11/1.50  --inst_learning_start                   3000
% 7.11/1.50  --inst_learning_factor                  2
% 7.11/1.50  --inst_start_prop_sim_after_learn       3
% 7.11/1.50  --inst_sel_renew                        solver
% 7.11/1.50  --inst_lit_activity_flag                true
% 7.11/1.50  --inst_restr_to_given                   false
% 7.11/1.50  --inst_activity_threshold               500
% 7.11/1.50  --inst_out_proof                        true
% 7.11/1.50  
% 7.11/1.50  ------ Resolution Options
% 7.11/1.50  
% 7.11/1.50  --resolution_flag                       true
% 7.11/1.50  --res_lit_sel                           adaptive
% 7.11/1.50  --res_lit_sel_side                      none
% 7.11/1.50  --res_ordering                          kbo
% 7.11/1.50  --res_to_prop_solver                    active
% 7.11/1.50  --res_prop_simpl_new                    false
% 7.11/1.50  --res_prop_simpl_given                  true
% 7.11/1.50  --res_passive_queue_type                priority_queues
% 7.11/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.11/1.50  --res_passive_queues_freq               [15;5]
% 7.11/1.50  --res_forward_subs                      full
% 7.11/1.50  --res_backward_subs                     full
% 7.11/1.50  --res_forward_subs_resolution           true
% 7.11/1.50  --res_backward_subs_resolution          true
% 7.11/1.50  --res_orphan_elimination                true
% 7.11/1.50  --res_time_limit                        2.
% 7.11/1.50  --res_out_proof                         true
% 7.11/1.50  
% 7.11/1.50  ------ Superposition Options
% 7.11/1.50  
% 7.11/1.50  --superposition_flag                    true
% 7.11/1.50  --sup_passive_queue_type                priority_queues
% 7.11/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.11/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.11/1.50  --demod_completeness_check              fast
% 7.11/1.50  --demod_use_ground                      true
% 7.11/1.50  --sup_to_prop_solver                    passive
% 7.11/1.50  --sup_prop_simpl_new                    true
% 7.11/1.50  --sup_prop_simpl_given                  true
% 7.11/1.50  --sup_fun_splitting                     false
% 7.11/1.50  --sup_smt_interval                      50000
% 7.11/1.50  
% 7.11/1.50  ------ Superposition Simplification Setup
% 7.11/1.50  
% 7.11/1.50  --sup_indices_passive                   []
% 7.11/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.11/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.50  --sup_full_bw                           [BwDemod]
% 7.11/1.50  --sup_immed_triv                        [TrivRules]
% 7.11/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.50  --sup_immed_bw_main                     []
% 7.11/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.11/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.50  
% 7.11/1.50  ------ Combination Options
% 7.11/1.50  
% 7.11/1.50  --comb_res_mult                         3
% 7.11/1.50  --comb_sup_mult                         2
% 7.11/1.50  --comb_inst_mult                        10
% 7.11/1.50  
% 7.11/1.50  ------ Debug Options
% 7.11/1.50  
% 7.11/1.50  --dbg_backtrace                         false
% 7.11/1.50  --dbg_dump_prop_clauses                 false
% 7.11/1.50  --dbg_dump_prop_clauses_file            -
% 7.11/1.50  --dbg_out_stat                          false
% 7.11/1.50  ------ Parsing...
% 7.11/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.11/1.50  
% 7.11/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.11/1.50  
% 7.11/1.50  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.11/1.50  
% 7.11/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.11/1.50  ------ Proving...
% 7.11/1.50  ------ Problem Properties 
% 7.11/1.50  
% 7.11/1.50  
% 7.11/1.50  clauses                                 32
% 7.11/1.50  conjectures                             7
% 7.11/1.50  EPR                                     7
% 7.11/1.50  Horn                                    26
% 7.11/1.50  unary                                   2
% 7.11/1.50  binary                                  11
% 7.11/1.50  lits                                    92
% 7.11/1.50  lits eq                                 3
% 7.11/1.50  fd_pure                                 0
% 7.11/1.50  fd_pseudo                               0
% 7.11/1.50  fd_cond                                 0
% 7.11/1.50  fd_pseudo_cond                          1
% 7.11/1.50  AC symbols                              0
% 7.11/1.50  
% 7.11/1.50  ------ Schedule dynamic 5 is on 
% 7.11/1.50  
% 7.11/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.11/1.50  
% 7.11/1.50  
% 7.11/1.50  ------ 
% 7.11/1.50  Current options:
% 7.11/1.50  ------ 
% 7.11/1.50  
% 7.11/1.50  ------ Input Options
% 7.11/1.50  
% 7.11/1.50  --out_options                           all
% 7.11/1.50  --tptp_safe_out                         true
% 7.11/1.50  --problem_path                          ""
% 7.11/1.50  --include_path                          ""
% 7.11/1.50  --clausifier                            res/vclausify_rel
% 7.11/1.50  --clausifier_options                    --mode clausify
% 7.11/1.50  --stdin                                 false
% 7.11/1.50  --stats_out                             all
% 7.11/1.50  
% 7.11/1.50  ------ General Options
% 7.11/1.50  
% 7.11/1.50  --fof                                   false
% 7.11/1.50  --time_out_real                         305.
% 7.11/1.50  --time_out_virtual                      -1.
% 7.11/1.50  --symbol_type_check                     false
% 7.11/1.50  --clausify_out                          false
% 7.11/1.50  --sig_cnt_out                           false
% 7.11/1.50  --trig_cnt_out                          false
% 7.11/1.50  --trig_cnt_out_tolerance                1.
% 7.11/1.50  --trig_cnt_out_sk_spl                   false
% 7.11/1.50  --abstr_cl_out                          false
% 7.11/1.50  
% 7.11/1.50  ------ Global Options
% 7.11/1.50  
% 7.11/1.50  --schedule                              default
% 7.11/1.50  --add_important_lit                     false
% 7.11/1.50  --prop_solver_per_cl                    1000
% 7.11/1.50  --min_unsat_core                        false
% 7.11/1.50  --soft_assumptions                      false
% 7.11/1.50  --soft_lemma_size                       3
% 7.11/1.50  --prop_impl_unit_size                   0
% 7.11/1.50  --prop_impl_unit                        []
% 7.11/1.50  --share_sel_clauses                     true
% 7.11/1.50  --reset_solvers                         false
% 7.11/1.50  --bc_imp_inh                            [conj_cone]
% 7.11/1.50  --conj_cone_tolerance                   3.
% 7.11/1.50  --extra_neg_conj                        none
% 7.11/1.50  --large_theory_mode                     true
% 7.11/1.50  --prolific_symb_bound                   200
% 7.11/1.50  --lt_threshold                          2000
% 7.11/1.50  --clause_weak_htbl                      true
% 7.11/1.50  --gc_record_bc_elim                     false
% 7.11/1.50  
% 7.11/1.50  ------ Preprocessing Options
% 7.11/1.50  
% 7.11/1.50  --preprocessing_flag                    true
% 7.11/1.50  --time_out_prep_mult                    0.1
% 7.11/1.50  --splitting_mode                        input
% 7.11/1.50  --splitting_grd                         true
% 7.11/1.50  --splitting_cvd                         false
% 7.11/1.50  --splitting_cvd_svl                     false
% 7.11/1.50  --splitting_nvd                         32
% 7.11/1.50  --sub_typing                            true
% 7.11/1.50  --prep_gs_sim                           true
% 7.11/1.50  --prep_unflatten                        true
% 7.11/1.50  --prep_res_sim                          true
% 7.11/1.50  --prep_upred                            true
% 7.11/1.50  --prep_sem_filter                       exhaustive
% 7.11/1.50  --prep_sem_filter_out                   false
% 7.11/1.50  --pred_elim                             true
% 7.11/1.50  --res_sim_input                         true
% 7.11/1.50  --eq_ax_congr_red                       true
% 7.11/1.50  --pure_diseq_elim                       true
% 7.11/1.50  --brand_transform                       false
% 7.11/1.50  --non_eq_to_eq                          false
% 7.11/1.50  --prep_def_merge                        true
% 7.11/1.50  --prep_def_merge_prop_impl              false
% 7.11/1.50  --prep_def_merge_mbd                    true
% 7.11/1.50  --prep_def_merge_tr_red                 false
% 7.11/1.50  --prep_def_merge_tr_cl                  false
% 7.11/1.50  --smt_preprocessing                     true
% 7.11/1.50  --smt_ac_axioms                         fast
% 7.11/1.50  --preprocessed_out                      false
% 7.11/1.50  --preprocessed_stats                    false
% 7.11/1.50  
% 7.11/1.50  ------ Abstraction refinement Options
% 7.11/1.50  
% 7.11/1.50  --abstr_ref                             []
% 7.11/1.50  --abstr_ref_prep                        false
% 7.11/1.50  --abstr_ref_until_sat                   false
% 7.11/1.50  --abstr_ref_sig_restrict                funpre
% 7.11/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.11/1.50  --abstr_ref_under                       []
% 7.11/1.50  
% 7.11/1.50  ------ SAT Options
% 7.11/1.50  
% 7.11/1.50  --sat_mode                              false
% 7.11/1.50  --sat_fm_restart_options                ""
% 7.11/1.50  --sat_gr_def                            false
% 7.11/1.50  --sat_epr_types                         true
% 7.11/1.50  --sat_non_cyclic_types                  false
% 7.11/1.50  --sat_finite_models                     false
% 7.11/1.50  --sat_fm_lemmas                         false
% 7.11/1.50  --sat_fm_prep                           false
% 7.11/1.50  --sat_fm_uc_incr                        true
% 7.11/1.50  --sat_out_model                         small
% 7.11/1.50  --sat_out_clauses                       false
% 7.11/1.50  
% 7.11/1.50  ------ QBF Options
% 7.11/1.50  
% 7.11/1.50  --qbf_mode                              false
% 7.11/1.50  --qbf_elim_univ                         false
% 7.11/1.50  --qbf_dom_inst                          none
% 7.11/1.50  --qbf_dom_pre_inst                      false
% 7.11/1.50  --qbf_sk_in                             false
% 7.11/1.50  --qbf_pred_elim                         true
% 7.11/1.50  --qbf_split                             512
% 7.11/1.50  
% 7.11/1.50  ------ BMC1 Options
% 7.11/1.50  
% 7.11/1.50  --bmc1_incremental                      false
% 7.11/1.50  --bmc1_axioms                           reachable_all
% 7.11/1.50  --bmc1_min_bound                        0
% 7.11/1.50  --bmc1_max_bound                        -1
% 7.11/1.50  --bmc1_max_bound_default                -1
% 7.11/1.50  --bmc1_symbol_reachability              true
% 7.11/1.50  --bmc1_property_lemmas                  false
% 7.11/1.50  --bmc1_k_induction                      false
% 7.11/1.50  --bmc1_non_equiv_states                 false
% 7.11/1.50  --bmc1_deadlock                         false
% 7.11/1.50  --bmc1_ucm                              false
% 7.11/1.50  --bmc1_add_unsat_core                   none
% 7.11/1.50  --bmc1_unsat_core_children              false
% 7.11/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.11/1.50  --bmc1_out_stat                         full
% 7.11/1.50  --bmc1_ground_init                      false
% 7.11/1.50  --bmc1_pre_inst_next_state              false
% 7.11/1.50  --bmc1_pre_inst_state                   false
% 7.11/1.50  --bmc1_pre_inst_reach_state             false
% 7.11/1.50  --bmc1_out_unsat_core                   false
% 7.11/1.50  --bmc1_aig_witness_out                  false
% 7.11/1.50  --bmc1_verbose                          false
% 7.11/1.50  --bmc1_dump_clauses_tptp                false
% 7.11/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.11/1.50  --bmc1_dump_file                        -
% 7.11/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.11/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.11/1.50  --bmc1_ucm_extend_mode                  1
% 7.11/1.50  --bmc1_ucm_init_mode                    2
% 7.11/1.50  --bmc1_ucm_cone_mode                    none
% 7.11/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.11/1.50  --bmc1_ucm_relax_model                  4
% 7.11/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.11/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.11/1.50  --bmc1_ucm_layered_model                none
% 7.11/1.50  --bmc1_ucm_max_lemma_size               10
% 7.11/1.50  
% 7.11/1.50  ------ AIG Options
% 7.11/1.50  
% 7.11/1.50  --aig_mode                              false
% 7.11/1.50  
% 7.11/1.50  ------ Instantiation Options
% 7.11/1.50  
% 7.11/1.50  --instantiation_flag                    true
% 7.11/1.50  --inst_sos_flag                         false
% 7.11/1.50  --inst_sos_phase                        true
% 7.11/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.11/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.11/1.50  --inst_lit_sel_side                     none
% 7.11/1.50  --inst_solver_per_active                1400
% 7.11/1.50  --inst_solver_calls_frac                1.
% 7.11/1.50  --inst_passive_queue_type               priority_queues
% 7.11/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.11/1.50  --inst_passive_queues_freq              [25;2]
% 7.11/1.50  --inst_dismatching                      true
% 7.11/1.50  --inst_eager_unprocessed_to_passive     true
% 7.11/1.50  --inst_prop_sim_given                   true
% 7.11/1.50  --inst_prop_sim_new                     false
% 7.11/1.50  --inst_subs_new                         false
% 7.11/1.50  --inst_eq_res_simp                      false
% 7.11/1.50  --inst_subs_given                       false
% 7.11/1.50  --inst_orphan_elimination               true
% 7.11/1.50  --inst_learning_loop_flag               true
% 7.11/1.50  --inst_learning_start                   3000
% 7.11/1.50  --inst_learning_factor                  2
% 7.11/1.50  --inst_start_prop_sim_after_learn       3
% 7.11/1.50  --inst_sel_renew                        solver
% 7.11/1.50  --inst_lit_activity_flag                true
% 7.11/1.50  --inst_restr_to_given                   false
% 7.11/1.50  --inst_activity_threshold               500
% 7.11/1.50  --inst_out_proof                        true
% 7.11/1.50  
% 7.11/1.50  ------ Resolution Options
% 7.11/1.50  
% 7.11/1.50  --resolution_flag                       false
% 7.11/1.50  --res_lit_sel                           adaptive
% 7.11/1.50  --res_lit_sel_side                      none
% 7.11/1.50  --res_ordering                          kbo
% 7.11/1.50  --res_to_prop_solver                    active
% 7.11/1.50  --res_prop_simpl_new                    false
% 7.11/1.50  --res_prop_simpl_given                  true
% 7.11/1.50  --res_passive_queue_type                priority_queues
% 7.11/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.11/1.50  --res_passive_queues_freq               [15;5]
% 7.11/1.50  --res_forward_subs                      full
% 7.11/1.50  --res_backward_subs                     full
% 7.11/1.50  --res_forward_subs_resolution           true
% 7.11/1.50  --res_backward_subs_resolution          true
% 7.11/1.50  --res_orphan_elimination                true
% 7.11/1.50  --res_time_limit                        2.
% 7.11/1.50  --res_out_proof                         true
% 7.11/1.50  
% 7.11/1.50  ------ Superposition Options
% 7.11/1.50  
% 7.11/1.50  --superposition_flag                    true
% 7.11/1.50  --sup_passive_queue_type                priority_queues
% 7.11/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.11/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.11/1.50  --demod_completeness_check              fast
% 7.11/1.50  --demod_use_ground                      true
% 7.11/1.50  --sup_to_prop_solver                    passive
% 7.11/1.50  --sup_prop_simpl_new                    true
% 7.11/1.50  --sup_prop_simpl_given                  true
% 7.11/1.50  --sup_fun_splitting                     false
% 7.11/1.50  --sup_smt_interval                      50000
% 7.11/1.50  
% 7.11/1.50  ------ Superposition Simplification Setup
% 7.11/1.50  
% 7.11/1.50  --sup_indices_passive                   []
% 7.11/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.11/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.50  --sup_full_bw                           [BwDemod]
% 7.11/1.50  --sup_immed_triv                        [TrivRules]
% 7.11/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.50  --sup_immed_bw_main                     []
% 7.11/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.11/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.50  
% 7.11/1.50  ------ Combination Options
% 7.11/1.50  
% 7.11/1.50  --comb_res_mult                         3
% 7.11/1.50  --comb_sup_mult                         2
% 7.11/1.50  --comb_inst_mult                        10
% 7.11/1.50  
% 7.11/1.50  ------ Debug Options
% 7.11/1.50  
% 7.11/1.50  --dbg_backtrace                         false
% 7.11/1.50  --dbg_dump_prop_clauses                 false
% 7.11/1.50  --dbg_dump_prop_clauses_file            -
% 7.11/1.50  --dbg_out_stat                          false
% 7.11/1.50  
% 7.11/1.50  
% 7.11/1.50  
% 7.11/1.50  
% 7.11/1.50  ------ Proving...
% 7.11/1.50  
% 7.11/1.50  
% 7.11/1.50  % SZS status Theorem for theBenchmark.p
% 7.11/1.50  
% 7.11/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.11/1.50  
% 7.11/1.50  fof(f8,axiom,(
% 7.11/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f22,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.11/1.50    inference(ennf_transformation,[],[f8])).
% 7.11/1.50  
% 7.11/1.50  fof(f23,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.11/1.50    inference(flattening,[],[f22])).
% 7.11/1.50  
% 7.11/1.50  fof(f39,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.11/1.50    inference(nnf_transformation,[],[f23])).
% 7.11/1.50  
% 7.11/1.50  fof(f65,plain,(
% 7.11/1.50    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f39])).
% 7.11/1.50  
% 7.11/1.50  fof(f9,axiom,(
% 7.11/1.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f24,plain,(
% 7.11/1.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.11/1.50    inference(ennf_transformation,[],[f9])).
% 7.11/1.50  
% 7.11/1.50  fof(f25,plain,(
% 7.11/1.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.11/1.50    inference(flattening,[],[f24])).
% 7.11/1.50  
% 7.11/1.50  fof(f67,plain,(
% 7.11/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f25])).
% 7.11/1.50  
% 7.11/1.50  fof(f12,conjecture,(
% 7.11/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f13,negated_conjecture,(
% 7.11/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 7.11/1.50    inference(negated_conjecture,[],[f12])).
% 7.11/1.50  
% 7.11/1.50  fof(f30,plain,(
% 7.11/1.50    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.11/1.50    inference(ennf_transformation,[],[f13])).
% 7.11/1.50  
% 7.11/1.50  fof(f31,plain,(
% 7.11/1.50    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.11/1.50    inference(flattening,[],[f30])).
% 7.11/1.50  
% 7.11/1.50  fof(f44,plain,(
% 7.11/1.50    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.11/1.50    inference(nnf_transformation,[],[f31])).
% 7.11/1.50  
% 7.11/1.50  fof(f45,plain,(
% 7.11/1.50    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.11/1.50    inference(flattening,[],[f44])).
% 7.11/1.50  
% 7.11/1.50  fof(f46,plain,(
% 7.11/1.50    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.11/1.50    inference(rectify,[],[f45])).
% 7.11/1.50  
% 7.11/1.50  fof(f50,plain,(
% 7.11/1.50    ( ! [X0,X1] : (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK5(X4),X1) & m1_connsp_2(sK5(X4),X0,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 7.11/1.50    introduced(choice_axiom,[])).
% 7.11/1.50  
% 7.11/1.50  fof(f49,plain,(
% 7.11/1.50    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 7.11/1.50    introduced(choice_axiom,[])).
% 7.11/1.50  
% 7.11/1.50  fof(f48,plain,(
% 7.11/1.50    ( ! [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(sK3,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK3) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.11/1.50    introduced(choice_axiom,[])).
% 7.11/1.50  
% 7.11/1.50  fof(f47,plain,(
% 7.11/1.50    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK2)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK2,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.11/1.50    introduced(choice_axiom,[])).
% 7.11/1.50  
% 7.11/1.50  fof(f51,plain,(
% 7.11/1.50    (((! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) & (! [X4] : ((r1_tarski(sK5(X4),sK3) & m1_connsp_2(sK5(X4),sK2,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.11/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f46,f50,f49,f48,f47])).
% 7.11/1.50  
% 7.11/1.50  fof(f74,plain,(
% 7.11/1.50    ~v2_struct_0(sK2)),
% 7.11/1.50    inference(cnf_transformation,[],[f51])).
% 7.11/1.50  
% 7.11/1.50  fof(f75,plain,(
% 7.11/1.50    v2_pre_topc(sK2)),
% 7.11/1.50    inference(cnf_transformation,[],[f51])).
% 7.11/1.50  
% 7.11/1.50  fof(f76,plain,(
% 7.11/1.50    l1_pre_topc(sK2)),
% 7.11/1.50    inference(cnf_transformation,[],[f51])).
% 7.11/1.50  
% 7.11/1.50  fof(f3,axiom,(
% 7.11/1.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f15,plain,(
% 7.11/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.11/1.50    inference(ennf_transformation,[],[f3])).
% 7.11/1.50  
% 7.11/1.50  fof(f16,plain,(
% 7.11/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.11/1.50    inference(flattening,[],[f15])).
% 7.11/1.50  
% 7.11/1.50  fof(f58,plain,(
% 7.11/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f16])).
% 7.11/1.50  
% 7.11/1.50  fof(f11,axiom,(
% 7.11/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f28,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.11/1.50    inference(ennf_transformation,[],[f11])).
% 7.11/1.50  
% 7.11/1.50  fof(f29,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.11/1.50    inference(flattening,[],[f28])).
% 7.11/1.50  
% 7.11/1.50  fof(f40,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.11/1.50    inference(nnf_transformation,[],[f29])).
% 7.11/1.50  
% 7.11/1.50  fof(f41,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.11/1.50    inference(rectify,[],[f40])).
% 7.11/1.50  
% 7.11/1.50  fof(f42,plain,(
% 7.11/1.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.11/1.50    introduced(choice_axiom,[])).
% 7.11/1.50  
% 7.11/1.50  fof(f43,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.11/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 7.11/1.50  
% 7.11/1.50  fof(f73,plain,(
% 7.11/1.50    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f43])).
% 7.11/1.50  
% 7.11/1.50  fof(f5,axiom,(
% 7.11/1.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f17,plain,(
% 7.11/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.11/1.50    inference(ennf_transformation,[],[f5])).
% 7.11/1.50  
% 7.11/1.50  fof(f18,plain,(
% 7.11/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.11/1.50    inference(flattening,[],[f17])).
% 7.11/1.50  
% 7.11/1.50  fof(f61,plain,(
% 7.11/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f18])).
% 7.11/1.50  
% 7.11/1.50  fof(f71,plain,(
% 7.11/1.50    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f43])).
% 7.11/1.50  
% 7.11/1.50  fof(f72,plain,(
% 7.11/1.50    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f43])).
% 7.11/1.50  
% 7.11/1.50  fof(f69,plain,(
% 7.11/1.50    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f43])).
% 7.11/1.50  
% 7.11/1.50  fof(f70,plain,(
% 7.11/1.50    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f43])).
% 7.11/1.50  
% 7.11/1.50  fof(f79,plain,(
% 7.11/1.50    ( ! [X4] : (m1_connsp_2(sK5(X4),sK2,X4) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f51])).
% 7.11/1.50  
% 7.11/1.50  fof(f80,plain,(
% 7.11/1.50    ( ! [X4] : (r1_tarski(sK5(X4),sK3) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f51])).
% 7.11/1.50  
% 7.11/1.50  fof(f77,plain,(
% 7.11/1.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 7.11/1.50    inference(cnf_transformation,[],[f51])).
% 7.11/1.50  
% 7.11/1.50  fof(f83,plain,(
% 7.11/1.50    ( ! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f51])).
% 7.11/1.50  
% 7.11/1.50  fof(f82,plain,(
% 7.11/1.50    r2_hidden(sK4,sK3) | ~v3_pre_topc(sK3,sK2)),
% 7.11/1.50    inference(cnf_transformation,[],[f51])).
% 7.11/1.50  
% 7.11/1.50  fof(f2,axiom,(
% 7.11/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f36,plain,(
% 7.11/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.11/1.50    inference(nnf_transformation,[],[f2])).
% 7.11/1.50  
% 7.11/1.50  fof(f37,plain,(
% 7.11/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.11/1.50    inference(flattening,[],[f36])).
% 7.11/1.50  
% 7.11/1.50  fof(f55,plain,(
% 7.11/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.11/1.50    inference(cnf_transformation,[],[f37])).
% 7.11/1.50  
% 7.11/1.50  fof(f85,plain,(
% 7.11/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.11/1.50    inference(equality_resolution,[],[f55])).
% 7.11/1.50  
% 7.11/1.50  fof(f10,axiom,(
% 7.11/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f26,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.11/1.50    inference(ennf_transformation,[],[f10])).
% 7.11/1.50  
% 7.11/1.50  fof(f27,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.11/1.50    inference(flattening,[],[f26])).
% 7.11/1.50  
% 7.11/1.50  fof(f68,plain,(
% 7.11/1.50    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f27])).
% 7.11/1.50  
% 7.11/1.50  fof(f1,axiom,(
% 7.11/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f14,plain,(
% 7.11/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.11/1.50    inference(ennf_transformation,[],[f1])).
% 7.11/1.50  
% 7.11/1.50  fof(f32,plain,(
% 7.11/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.11/1.50    inference(nnf_transformation,[],[f14])).
% 7.11/1.50  
% 7.11/1.50  fof(f33,plain,(
% 7.11/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.11/1.50    inference(rectify,[],[f32])).
% 7.11/1.50  
% 7.11/1.50  fof(f34,plain,(
% 7.11/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.11/1.50    introduced(choice_axiom,[])).
% 7.11/1.50  
% 7.11/1.50  fof(f35,plain,(
% 7.11/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.11/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 7.11/1.50  
% 7.11/1.50  fof(f53,plain,(
% 7.11/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f35])).
% 7.11/1.50  
% 7.11/1.50  fof(f54,plain,(
% 7.11/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f35])).
% 7.11/1.50  
% 7.11/1.50  fof(f57,plain,(
% 7.11/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f37])).
% 7.11/1.50  
% 7.11/1.50  fof(f7,axiom,(
% 7.11/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f20,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.11/1.50    inference(ennf_transformation,[],[f7])).
% 7.11/1.50  
% 7.11/1.50  fof(f21,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.11/1.50    inference(flattening,[],[f20])).
% 7.11/1.50  
% 7.11/1.50  fof(f64,plain,(
% 7.11/1.50    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f21])).
% 7.11/1.50  
% 7.11/1.50  fof(f6,axiom,(
% 7.11/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.11/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.50  
% 7.11/1.50  fof(f19,plain,(
% 7.11/1.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.11/1.50    inference(ennf_transformation,[],[f6])).
% 7.11/1.50  
% 7.11/1.50  fof(f62,plain,(
% 7.11/1.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.11/1.50    inference(cnf_transformation,[],[f19])).
% 7.11/1.50  
% 7.11/1.50  cnf(c_14,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_15,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_212,plain,
% 7.11/1.50      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_14,c_15]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_213,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(renaming,[status(thm)],[c_212]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_31,negated_conjecture,
% 7.11/1.50      ( ~ v2_struct_0(sK2) ),
% 7.11/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_440,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1)
% 7.11/1.50      | sK2 != X1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_213,c_31]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_441,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 7.11/1.50      | ~ v2_pre_topc(sK2)
% 7.11/1.50      | ~ l1_pre_topc(sK2) ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_440]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_30,negated_conjecture,
% 7.11/1.50      ( v2_pre_topc(sK2) ),
% 7.11/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_29,negated_conjecture,
% 7.11/1.50      ( l1_pre_topc(sK2) ),
% 7.11/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_445,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_441,c_30,c_29]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_23469,plain,
% 7.11/1.50      ( ~ m1_connsp_2(sK3,sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
% 7.11/1.50      | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 7.11/1.50      | r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3)) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_445]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_6,plain,
% 7.11/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.11/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5097,plain,
% 7.11/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK3) | r1_tarski(X0,sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11125,plain,
% 7.11/1.50      ( ~ r1_tarski(X0,sK5(sK0(sK3,k1_tops_1(sK2,sK3))))
% 7.11/1.50      | r1_tarski(X0,sK3)
% 7.11/1.50      | ~ r1_tarski(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_5097]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_16736,plain,
% 7.11/1.50      ( ~ r1_tarski(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK5(sK0(sK3,k1_tops_1(sK2,sK3))))
% 7.11/1.50      | r1_tarski(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK3)
% 7.11/1.50      | ~ r1_tarski(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_11125]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_17,plain,
% 7.11/1.50      ( m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ v3_pre_topc(X3,X1)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | ~ r2_hidden(X2,X3)
% 7.11/1.50      | ~ r1_tarski(X3,X0)
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_545,plain,
% 7.11/1.50      ( m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ v3_pre_topc(X3,X1)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | ~ r2_hidden(X2,X3)
% 7.11/1.50      | ~ r1_tarski(X3,X0)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1)
% 7.11/1.50      | sK2 != X1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_31]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_546,plain,
% 7.11/1.50      ( m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ v3_pre_topc(X2,sK2)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(X1,X2)
% 7.11/1.50      | ~ r1_tarski(X2,X0)
% 7.11/1.50      | ~ v2_pre_topc(sK2)
% 7.11/1.50      | ~ l1_pre_topc(sK2) ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_545]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_550,plain,
% 7.11/1.50      ( m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ v3_pre_topc(X2,sK2)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(X1,X2)
% 7.11/1.50      | ~ r1_tarski(X2,X0) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_546,c_30,c_29]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_551,plain,
% 7.11/1.50      ( m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ v3_pre_topc(X2,sK2)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(X1,X2)
% 7.11/1.50      | ~ r1_tarski(X2,X0) ),
% 7.11/1.50      inference(renaming,[status(thm)],[c_550]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_9,plain,
% 7.11/1.50      ( m1_subset_1(X0,X1)
% 7.11/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.11/1.50      | ~ r2_hidden(X0,X2) ),
% 7.11/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_570,plain,
% 7.11/1.50      ( m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ v3_pre_topc(X2,sK2)
% 7.11/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(X1,X2)
% 7.11/1.50      | ~ r1_tarski(X2,X0) ),
% 7.11/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_551,c_9]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_7790,plain,
% 7.11/1.50      ( m1_connsp_2(X0,sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
% 7.11/1.50      | ~ v3_pre_topc(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK2)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ m1_subset_1(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))))
% 7.11/1.50      | ~ r1_tarski(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),X0) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_570]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_15324,plain,
% 7.11/1.50      ( m1_connsp_2(sK3,sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
% 7.11/1.50      | ~ v3_pre_topc(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK2)
% 7.11/1.50      | ~ m1_subset_1(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))))
% 7.11/1.50      | ~ r1_tarski(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_7790]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_19,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | r1_tarski(sK1(X1,X2,X0),X0)
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_195,plain,
% 7.11/1.50      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | r1_tarski(sK1(X1,X2,X0),X0)
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_19,c_15]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_196,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | r1_tarski(sK1(X1,X2,X0),X0)
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(renaming,[status(thm)],[c_195]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_482,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | r1_tarski(sK1(X1,X2,X0),X0)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1)
% 7.11/1.50      | sK2 != X1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_196,c_31]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_483,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | r1_tarski(sK1(sK2,X1,X0),X0)
% 7.11/1.50      | ~ v2_pre_topc(sK2)
% 7.11/1.50      | ~ l1_pre_topc(sK2) ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_482]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_487,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | r1_tarski(sK1(sK2,X1,X0),X0) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_483,c_30,c_29]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_7129,plain,
% 7.11/1.50      ( ~ m1_connsp_2(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
% 7.11/1.50      | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 7.11/1.50      | r1_tarski(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_487]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_18,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | r2_hidden(X2,sK1(X1,X2,X0))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_202,plain,
% 7.11/1.50      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | r2_hidden(X2,sK1(X1,X2,X0))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_18,c_15]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_203,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | r2_hidden(X2,sK1(X1,X2,X0))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(renaming,[status(thm)],[c_202]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_461,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | r2_hidden(X2,sK1(X1,X2,X0))
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1)
% 7.11/1.50      | sK2 != X1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_203,c_31]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_462,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | r2_hidden(X1,sK1(sK2,X1,X0))
% 7.11/1.50      | ~ v2_pre_topc(sK2)
% 7.11/1.50      | ~ l1_pre_topc(sK2) ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_461]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_466,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | r2_hidden(X1,sK1(sK2,X1,X0)) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_462,c_30,c_29]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_7126,plain,
% 7.11/1.50      ( ~ m1_connsp_2(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
% 7.11/1.50      | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 7.11/1.50      | r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3))))) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_466]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_21,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_181,plain,
% 7.11/1.50      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_21,c_15]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_182,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(renaming,[status(thm)],[c_181]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_524,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1)
% 7.11/1.50      | sK2 != X1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_182,c_31]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_525,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ v2_pre_topc(sK2)
% 7.11/1.50      | ~ l1_pre_topc(sK2) ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_524]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_529,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_525,c_30,c_29]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_7123,plain,
% 7.11/1.50      ( ~ m1_connsp_2(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
% 7.11/1.50      | m1_subset_1(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2)) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_529]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_20,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_188,plain,
% 7.11/1.50      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 7.11/1.50      | ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_20,c_15]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_189,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(renaming,[status(thm)],[c_188]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_503,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1)
% 7.11/1.50      | sK2 != X1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_189,c_31]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_504,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | v3_pre_topc(sK1(sK2,X1,X0),sK2)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | ~ v2_pre_topc(sK2)
% 7.11/1.50      | ~ l1_pre_topc(sK2) ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_503]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_508,plain,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | v3_pre_topc(sK1(sK2,X1,X0),sK2)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_504,c_30,c_29]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_7068,plain,
% 7.11/1.50      ( ~ m1_connsp_2(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
% 7.11/1.50      | v3_pre_topc(sK1(sK2,sK0(sK3,k1_tops_1(sK2,sK3)),sK5(sK0(sK3,k1_tops_1(sK2,sK3)))),sK2)
% 7.11/1.50      | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2)) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_508]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5682,plain,
% 7.11/1.50      ( m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),X0)
% 7.11/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 7.11/1.50      | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_6548,plain,
% 7.11/1.50      ( m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 7.11/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_5682]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_26,negated_conjecture,
% 7.11/1.50      ( m1_connsp_2(sK5(X0),sK2,X0)
% 7.11/1.50      | v3_pre_topc(sK3,sK2)
% 7.11/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.11/1.50      | ~ r2_hidden(X0,sK3) ),
% 7.11/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5690,plain,
% 7.11/1.50      ( m1_connsp_2(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK2,sK0(sK3,k1_tops_1(sK2,sK3)))
% 7.11/1.50      | v3_pre_topc(sK3,sK2)
% 7.11/1.50      | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 7.11/1.50      | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_26]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_25,negated_conjecture,
% 7.11/1.50      ( v3_pre_topc(sK3,sK2)
% 7.11/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.11/1.50      | ~ r2_hidden(X0,sK3)
% 7.11/1.50      | r1_tarski(sK5(X0),sK3) ),
% 7.11/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5692,plain,
% 7.11/1.50      ( v3_pre_topc(sK3,sK2)
% 7.11/1.50      | ~ m1_subset_1(sK0(sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 7.11/1.50      | ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK3)
% 7.11/1.50      | r1_tarski(sK5(sK0(sK3,k1_tops_1(sK2,sK3))),sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_25]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_28,negated_conjecture,
% 7.11/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.11/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4465,plain,
% 7.11/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_22,negated_conjecture,
% 7.11/1.50      ( ~ m1_connsp_2(X0,sK2,sK4)
% 7.11/1.50      | ~ v3_pre_topc(sK3,sK2)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r1_tarski(X0,sK3) ),
% 7.11/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4471,plain,
% 7.11/1.50      ( m1_connsp_2(X0,sK2,sK4) != iProver_top
% 7.11/1.50      | v3_pre_topc(sK3,sK2) != iProver_top
% 7.11/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.11/1.50      | r1_tarski(X0,sK3) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4744,plain,
% 7.11/1.50      ( m1_connsp_2(sK3,sK2,sK4) != iProver_top
% 7.11/1.50      | v3_pre_topc(sK3,sK2) != iProver_top
% 7.11/1.50      | r1_tarski(sK3,sK3) != iProver_top ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_4465,c_4471]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_35,plain,
% 7.11/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_23,negated_conjecture,
% 7.11/1.50      ( ~ v3_pre_topc(sK3,sK2) | r2_hidden(sK4,sK3) ),
% 7.11/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_46,plain,
% 7.11/1.50      ( v3_pre_topc(sK3,sK2) != iProver_top
% 7.11/1.50      | r2_hidden(sK4,sK3) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5,plain,
% 7.11/1.50      ( r1_tarski(X0,X0) ),
% 7.11/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5092,plain,
% 7.11/1.50      ( r1_tarski(sK3,sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5095,plain,
% 7.11/1.50      ( r1_tarski(sK3,sK3) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_5092]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_16,plain,
% 7.11/1.50      ( m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ v3_pre_topc(X0,X1)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | ~ r2_hidden(X2,X0)
% 7.11/1.50      | v2_struct_0(X1)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_580,plain,
% 7.11/1.50      ( m1_connsp_2(X0,X1,X2)
% 7.11/1.50      | ~ v3_pre_topc(X0,X1)
% 7.11/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | ~ r2_hidden(X2,X0)
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1)
% 7.11/1.50      | sK2 != X1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_581,plain,
% 7.11/1.50      ( m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ v3_pre_topc(X0,sK2)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(X1,X0)
% 7.11/1.50      | ~ v2_pre_topc(sK2)
% 7.11/1.50      | ~ l1_pre_topc(sK2) ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_580]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_585,plain,
% 7.11/1.50      ( m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ v3_pre_topc(X0,sK2)
% 7.11/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(X1,X0) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_581,c_30,c_29]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_601,plain,
% 7.11/1.50      ( m1_connsp_2(X0,sK2,X1)
% 7.11/1.50      | ~ v3_pre_topc(X0,sK2)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(X1,X0) ),
% 7.11/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_585,c_9]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5115,plain,
% 7.11/1.50      ( m1_connsp_2(sK3,sK2,sK4)
% 7.11/1.50      | ~ v3_pre_topc(sK3,sK2)
% 7.11/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ r2_hidden(sK4,sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_601]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5116,plain,
% 7.11/1.50      ( m1_connsp_2(sK3,sK2,sK4) = iProver_top
% 7.11/1.50      | v3_pre_topc(sK3,sK2) != iProver_top
% 7.11/1.50      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.11/1.50      | r2_hidden(sK4,sK3) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_5115]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5203,plain,
% 7.11/1.50      ( v3_pre_topc(sK3,sK2) != iProver_top ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_4744,c_35,c_46,c_5095,c_5116]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5205,plain,
% 7.11/1.50      ( ~ v3_pre_topc(sK3,sK2) ),
% 7.11/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_5203]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_1,plain,
% 7.11/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4835,plain,
% 7.11/1.50      ( r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),sK3)
% 7.11/1.50      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_0,plain,
% 7.11/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4836,plain,
% 7.11/1.50      ( ~ r2_hidden(sK0(sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
% 7.11/1.50      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_3,plain,
% 7.11/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.11/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4786,plain,
% 7.11/1.50      ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 7.11/1.50      | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
% 7.11/1.50      | k1_tops_1(sK2,sK3) = sK3 ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11,plain,
% 7.11/1.50      ( v3_pre_topc(X0,X1)
% 7.11/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | ~ v2_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X3)
% 7.11/1.50      | k1_tops_1(X1,X0) != X0 ),
% 7.11/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_695,plain,
% 7.11/1.50      ( v3_pre_topc(X0,X1)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.11/1.50      | ~ l1_pre_topc(X1)
% 7.11/1.50      | ~ l1_pre_topc(X3)
% 7.11/1.50      | k1_tops_1(X1,X0) != X0
% 7.11/1.50      | sK2 != X1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_30]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_696,plain,
% 7.11/1.50      ( v3_pre_topc(X0,sK2)
% 7.11/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ l1_pre_topc(X2)
% 7.11/1.50      | ~ l1_pre_topc(sK2)
% 7.11/1.50      | k1_tops_1(sK2,X0) != X0 ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_695]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_700,plain,
% 7.11/1.50      ( ~ l1_pre_topc(X2)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.11/1.50      | v3_pre_topc(X0,sK2)
% 7.11/1.50      | k1_tops_1(sK2,X0) != X0 ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_696,c_29]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_701,plain,
% 7.11/1.50      ( v3_pre_topc(X0,sK2)
% 7.11/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ l1_pre_topc(X2)
% 7.11/1.50      | k1_tops_1(sK2,X0) != X0 ),
% 7.11/1.50      inference(renaming,[status(thm)],[c_700]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_787,plain,
% 7.11/1.50      ( v3_pre_topc(X0,sK2)
% 7.11/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | k1_tops_1(sK2,X0) != X0
% 7.11/1.50      | sK2 != X2 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_29,c_701]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_788,plain,
% 7.11/1.50      ( v3_pre_topc(X0,sK2)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | k1_tops_1(sK2,X0) != X0 ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_787]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_3760,plain,
% 7.11/1.50      ( v3_pre_topc(X0,sK2)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | k1_tops_1(sK2,X0) != X0
% 7.11/1.50      | ~ sP1_iProver_split ),
% 7.11/1.50      inference(splitting,
% 7.11/1.50                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.11/1.50                [c_788]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_3761,plain,
% 7.11/1.50      ( sP1_iProver_split | sP0_iProver_split ),
% 7.11/1.50      inference(splitting,
% 7.11/1.50                [splitting(split),new_symbols(definition,[])],
% 7.11/1.50                [c_788]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_3759,plain,
% 7.11/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | ~ sP0_iProver_split ),
% 7.11/1.50      inference(splitting,
% 7.11/1.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.11/1.50                [c_788]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_3865,plain,
% 7.11/1.50      ( k1_tops_1(sK2,X0) != X0
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | v3_pre_topc(X0,sK2) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_3760,c_3761,c_3759]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_3866,plain,
% 7.11/1.50      ( v3_pre_topc(X0,sK2)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | k1_tops_1(sK2,X0) != X0 ),
% 7.11/1.50      inference(renaming,[status(thm)],[c_3865]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4728,plain,
% 7.11/1.50      ( v3_pre_topc(sK3,sK2)
% 7.11/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | k1_tops_1(sK2,sK3) != sK3 ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_3866]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4729,plain,
% 7.11/1.50      ( k1_tops_1(sK2,sK3) != sK3
% 7.11/1.50      | v3_pre_topc(sK3,sK2) = iProver_top
% 7.11/1.50      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_4728]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_10,plain,
% 7.11/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.11/1.50      | ~ l1_pre_topc(X1) ),
% 7.11/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_775,plain,
% 7.11/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.11/1.50      | sK2 != X1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_776,plain,
% 7.11/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | r1_tarski(k1_tops_1(sK2,X0),X0) ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_775]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4725,plain,
% 7.11/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.11/1.50      | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_776]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(contradiction,plain,
% 7.11/1.50      ( $false ),
% 7.11/1.50      inference(minisat,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_23469,c_16736,c_15324,c_7129,c_7126,c_7123,c_7068,
% 7.11/1.50                 c_6548,c_5690,c_5692,c_5205,c_5203,c_4835,c_4836,c_4786,
% 7.11/1.50                 c_4729,c_4725,c_35,c_28]) ).
% 7.11/1.50  
% 7.11/1.50  
% 7.11/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.11/1.50  
% 7.11/1.50  ------                               Statistics
% 7.11/1.50  
% 7.11/1.50  ------ General
% 7.11/1.50  
% 7.11/1.50  abstr_ref_over_cycles:                  0
% 7.11/1.50  abstr_ref_under_cycles:                 0
% 7.11/1.50  gc_basic_clause_elim:                   0
% 7.11/1.50  forced_gc_time:                         0
% 7.11/1.50  parsing_time:                           0.007
% 7.11/1.50  unif_index_cands_time:                  0.
% 7.11/1.50  unif_index_add_time:                    0.
% 7.11/1.50  orderings_time:                         0.
% 7.11/1.50  out_proof_time:                         0.018
% 7.11/1.50  total_time:                             0.525
% 7.11/1.50  num_of_symbols:                         51
% 7.11/1.50  num_of_terms:                           13210
% 7.11/1.50  
% 7.11/1.50  ------ Preprocessing
% 7.11/1.50  
% 7.11/1.50  num_of_splits:                          4
% 7.11/1.50  num_of_split_atoms:                     3
% 7.11/1.50  num_of_reused_defs:                     1
% 7.11/1.50  num_eq_ax_congr_red:                    20
% 7.11/1.50  num_of_sem_filtered_clauses:            4
% 7.11/1.50  num_of_subtypes:                        0
% 7.11/1.50  monotx_restored_types:                  0
% 7.11/1.50  sat_num_of_epr_types:                   0
% 7.11/1.50  sat_num_of_non_cyclic_types:            0
% 7.11/1.50  sat_guarded_non_collapsed_types:        0
% 7.11/1.50  num_pure_diseq_elim:                    0
% 7.11/1.50  simp_replaced_by:                       0
% 7.11/1.50  res_preprocessed:                       141
% 7.11/1.50  prep_upred:                             0
% 7.11/1.50  prep_unflattend:                        86
% 7.11/1.50  smt_new_axioms:                         0
% 7.11/1.50  pred_elim_cands:                        5
% 7.11/1.50  pred_elim:                              3
% 7.11/1.50  pred_elim_cl:                           3
% 7.11/1.50  pred_elim_cycles:                       7
% 7.11/1.50  merged_defs:                            8
% 7.11/1.50  merged_defs_ncl:                        0
% 7.11/1.50  bin_hyper_res:                          8
% 7.11/1.50  prep_cycles:                            4
% 7.11/1.50  pred_elim_time:                         0.041
% 7.11/1.50  splitting_time:                         0.
% 7.11/1.50  sem_filter_time:                        0.
% 7.11/1.50  monotx_time:                            0.
% 7.11/1.50  subtype_inf_time:                       0.
% 7.11/1.50  
% 7.11/1.50  ------ Problem properties
% 7.11/1.50  
% 7.11/1.50  clauses:                                32
% 7.11/1.50  conjectures:                            7
% 7.11/1.50  epr:                                    7
% 7.11/1.50  horn:                                   26
% 7.11/1.50  ground:                                 5
% 7.11/1.50  unary:                                  2
% 7.11/1.50  binary:                                 11
% 7.11/1.50  lits:                                   92
% 7.11/1.50  lits_eq:                                3
% 7.11/1.50  fd_pure:                                0
% 7.11/1.50  fd_pseudo:                              0
% 7.11/1.50  fd_cond:                                0
% 7.11/1.50  fd_pseudo_cond:                         1
% 7.11/1.50  ac_symbols:                             0
% 7.11/1.50  
% 7.11/1.50  ------ Propositional Solver
% 7.11/1.50  
% 7.11/1.50  prop_solver_calls:                      33
% 7.11/1.50  prop_fast_solver_calls:                 2635
% 7.11/1.50  smt_solver_calls:                       0
% 7.11/1.50  smt_fast_solver_calls:                  0
% 7.11/1.50  prop_num_of_clauses:                    6736
% 7.11/1.50  prop_preprocess_simplified:             14215
% 7.11/1.50  prop_fo_subsumed:                       129
% 7.11/1.50  prop_solver_time:                       0.
% 7.11/1.50  smt_solver_time:                        0.
% 7.11/1.50  smt_fast_solver_time:                   0.
% 7.11/1.50  prop_fast_solver_time:                  0.
% 7.11/1.50  prop_unsat_core_time:                   0.
% 7.11/1.50  
% 7.11/1.50  ------ QBF
% 7.11/1.50  
% 7.11/1.50  qbf_q_res:                              0
% 7.11/1.50  qbf_num_tautologies:                    0
% 7.11/1.50  qbf_prep_cycles:                        0
% 7.11/1.50  
% 7.11/1.50  ------ BMC1
% 7.11/1.50  
% 7.11/1.50  bmc1_current_bound:                     -1
% 7.11/1.50  bmc1_last_solved_bound:                 -1
% 7.11/1.50  bmc1_unsat_core_size:                   -1
% 7.11/1.50  bmc1_unsat_core_parents_size:           -1
% 7.11/1.50  bmc1_merge_next_fun:                    0
% 7.11/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.11/1.50  
% 7.11/1.50  ------ Instantiation
% 7.11/1.50  
% 7.11/1.50  inst_num_of_clauses:                    1467
% 7.11/1.50  inst_num_in_passive:                    803
% 7.11/1.50  inst_num_in_active:                     627
% 7.11/1.50  inst_num_in_unprocessed:                36
% 7.11/1.50  inst_num_of_loops:                      933
% 7.11/1.50  inst_num_of_learning_restarts:          0
% 7.11/1.50  inst_num_moves_active_passive:          299
% 7.11/1.50  inst_lit_activity:                      0
% 7.11/1.50  inst_lit_activity_moves:                0
% 7.11/1.50  inst_num_tautologies:                   0
% 7.11/1.50  inst_num_prop_implied:                  0
% 7.11/1.50  inst_num_existing_simplified:           0
% 7.11/1.50  inst_num_eq_res_simplified:             0
% 7.11/1.50  inst_num_child_elim:                    0
% 7.11/1.50  inst_num_of_dismatching_blockings:      967
% 7.11/1.50  inst_num_of_non_proper_insts:           2039
% 7.11/1.50  inst_num_of_duplicates:                 0
% 7.11/1.50  inst_inst_num_from_inst_to_res:         0
% 7.11/1.50  inst_dismatching_checking_time:         0.
% 7.11/1.50  
% 7.11/1.50  ------ Resolution
% 7.11/1.50  
% 7.11/1.50  res_num_of_clauses:                     0
% 7.11/1.50  res_num_in_passive:                     0
% 7.11/1.50  res_num_in_active:                      0
% 7.11/1.50  res_num_of_loops:                       145
% 7.11/1.50  res_forward_subset_subsumed:            136
% 7.11/1.50  res_backward_subset_subsumed:           0
% 7.11/1.50  res_forward_subsumed:                   0
% 7.11/1.50  res_backward_subsumed:                  0
% 7.11/1.50  res_forward_subsumption_resolution:     16
% 7.11/1.50  res_backward_subsumption_resolution:    0
% 7.11/1.50  res_clause_to_clause_subsumption:       4510
% 7.11/1.50  res_orphan_elimination:                 0
% 7.11/1.50  res_tautology_del:                      232
% 7.11/1.50  res_num_eq_res_simplified:              0
% 7.11/1.50  res_num_sel_changes:                    0
% 7.11/1.50  res_moves_from_active_to_pass:          0
% 7.11/1.50  
% 7.11/1.50  ------ Superposition
% 7.11/1.50  
% 7.11/1.50  sup_time_total:                         0.
% 7.11/1.50  sup_time_generating:                    0.
% 7.11/1.50  sup_time_sim_full:                      0.
% 7.11/1.50  sup_time_sim_immed:                     0.
% 7.11/1.50  
% 7.11/1.50  sup_num_of_clauses:                     526
% 7.11/1.50  sup_num_in_active:                      183
% 7.11/1.50  sup_num_in_passive:                     343
% 7.11/1.50  sup_num_of_loops:                       186
% 7.11/1.50  sup_fw_superposition:                   355
% 7.11/1.50  sup_bw_superposition:                   395
% 7.11/1.50  sup_immediate_simplified:               134
% 7.11/1.50  sup_given_eliminated:                   1
% 7.11/1.50  comparisons_done:                       0
% 7.11/1.50  comparisons_avoided:                    0
% 7.11/1.50  
% 7.11/1.50  ------ Simplifications
% 7.11/1.50  
% 7.11/1.50  
% 7.11/1.50  sim_fw_subset_subsumed:                 79
% 7.11/1.50  sim_bw_subset_subsumed:                 22
% 7.11/1.50  sim_fw_subsumed:                        51
% 7.11/1.50  sim_bw_subsumed:                        2
% 7.11/1.50  sim_fw_subsumption_res:                 8
% 7.11/1.50  sim_bw_subsumption_res:                 0
% 7.11/1.50  sim_tautology_del:                      24
% 7.11/1.50  sim_eq_tautology_del:                   6
% 7.11/1.50  sim_eq_res_simp:                        0
% 7.11/1.50  sim_fw_demodulated:                     0
% 7.11/1.50  sim_bw_demodulated:                     0
% 7.11/1.50  sim_light_normalised:                   0
% 7.11/1.50  sim_joinable_taut:                      0
% 7.11/1.50  sim_joinable_simp:                      0
% 7.11/1.50  sim_ac_normalised:                      0
% 7.11/1.50  sim_smt_subsumption:                    0
% 7.11/1.50  
%------------------------------------------------------------------------------
