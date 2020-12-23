%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:23 EST 2020

% Result     : Theorem 1.42s
% Output     : CNFRefutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 625 expanded)
%              Number of clauses        :   75 ( 116 expanded)
%              Number of leaves         :   18 ( 188 expanded)
%              Depth                    :   17
%              Number of atoms          :  749 (7010 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X2,X3)
              & r1_tarski(X3,X1)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r1_tarski(X3,X1)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X2,X3)
                  & r1_tarski(X3,X1)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r1_tarski(X3,X1)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X2,X3)
                  & r1_tarski(X3,X1)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r1_tarski(X3,X0)
                  | ~ v3_pre_topc(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,X0) )
            & ( ? [X4] :
                  ( r2_hidden(X2,X4)
                  & r1_tarski(X4,X0)
                  & v3_pre_topc(X4,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,X0) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X0)
              | ! [X6] :
                  ( ~ r2_hidden(X5,X6)
                  | ~ r1_tarski(X6,X0)
                  | ~ v3_pre_topc(X6,X1)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
            & ( ? [X7] :
                  ( r2_hidden(X5,X7)
                  & r1_tarski(X7,X0)
                  & v3_pre_topc(X7,X1)
                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X5,X0) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( r2_hidden(X5,X7)
          & r1_tarski(X7,X0)
          & v3_pre_topc(X7,X1)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(X5,sK4(X0,X1,X5))
        & r1_tarski(sK4(X0,X1,X5),X0)
        & v3_pre_topc(sK4(X0,X1,X5),X1)
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X2,X4)
          & r1_tarski(X4,X0)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(X2,sK3(X0,X1))
        & r1_tarski(sK3(X0,X1),X0)
        & v3_pre_topc(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X2,X3)
                | ~ r1_tarski(X3,X0)
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,X0) )
          & ( ? [X4] :
                ( r2_hidden(X2,X4)
                & r1_tarski(X4,X0)
                & v3_pre_topc(X4,X1)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,X0) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(sK2(X0,X1),X3)
              | ~ r1_tarski(X3,X0)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( ? [X4] :
              ( r2_hidden(sK2(X0,X1),X4)
              & r1_tarski(X4,X0)
              & v3_pre_topc(X4,X1)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( ~ r2_hidden(sK2(X0,X1),X3)
                | ~ r1_tarski(X3,X0)
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1),X0) )
          & ( ( r2_hidden(sK2(X0,X1),sK3(X0,X1))
              & r1_tarski(sK3(X0,X1),X0)
              & v3_pre_topc(sK3(X0,X1),X1)
              & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1),X0) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X0)
              | ! [X6] :
                  ( ~ r2_hidden(X5,X6)
                  | ~ r1_tarski(X6,X0)
                  | ~ v3_pre_topc(X6,X1)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
            & ( ( r2_hidden(X5,sK4(X0,X1,X5))
                & r1_tarski(sK4(X0,X1,X5),X0)
                & v3_pre_topc(sK4(X0,X1,X5),X1)
                & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X5,X0) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X0)
      | ~ r2_hidden(X5,X6)
      | ~ r1_tarski(X6,X0)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK8)
        & r1_tarski(sK8,X2)
        & v3_pre_topc(sK8,X0)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
              | ~ r1_tarski(X3,sK7)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_connsp_2(sK7,X0,X1) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,sK7)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | m1_connsp_2(sK7,X0,X1) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
                  ( ~ r2_hidden(sK6,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,sK6) )
            & ( ? [X4] :
                  ( r2_hidden(sK6,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | m1_connsp_2(X2,X0,sK6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
                    | ~ v3_pre_topc(X3,sK5)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) )
                | ~ m1_connsp_2(X2,sK5,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK5)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK5))) )
                | m1_connsp_2(X2,sK5,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK6,X3)
          | ~ r1_tarski(X3,sK7)
          | ~ v3_pre_topc(X3,sK5)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) )
      | ~ m1_connsp_2(sK7,sK5,sK6) )
    & ( ( r2_hidden(sK6,sK8)
        & r1_tarski(sK8,sK7)
        & v3_pre_topc(sK8,sK5)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) )
      | m1_connsp_2(sK7,sK5,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f40,f44,f43,f42,f41])).

fof(f70,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v3_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v3_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f27,f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK6,X3)
      | ~ r1_tarski(X3,sK7)
      | ~ v3_pre_topc(X3,sK5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ m1_connsp_2(sK7,sK5,sK6) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,
    ( r2_hidden(sK6,sK8)
    | m1_connsp_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,
    ( r1_tarski(sK8,sK7)
    | m1_connsp_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,
    ( v3_pre_topc(sK8,sK5)
    | m1_connsp_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_connsp_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ sP0(X2,X3)
    | ~ v3_pre_topc(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3827,plain,
    ( ~ r2_hidden(X0_48,X0_49)
    | r2_hidden(X0_48,X1_49)
    | ~ sP0(X1_49,X0_50)
    | ~ v3_pre_topc(X0_49,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(X0_50)))
    | ~ r1_tarski(X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4252,plain,
    ( r2_hidden(sK6,X0_49)
    | ~ r2_hidden(sK6,sK8)
    | ~ sP0(X0_49,X0_50)
    | ~ v3_pre_topc(sK8,X0_50)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0_50)))
    | ~ r1_tarski(sK8,X0_49) ),
    inference(instantiation,[status(thm)],[c_3827])).

cnf(c_4618,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,X0_49))
    | ~ r2_hidden(sK6,sK8)
    | ~ sP0(k1_tops_1(sK5,X0_49),sK5)
    | ~ v3_pre_topc(sK8,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(sK8,k1_tops_1(sK5,X0_49)) ),
    inference(instantiation,[status(thm)],[c_4252])).

cnf(c_4620,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ r2_hidden(sK6,sK8)
    | ~ sP0(k1_tops_1(sK5,sK7),sK5)
    | ~ v3_pre_topc(sK8,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(sK8,k1_tops_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_4618])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_616,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK5,X1)) ),
    inference(resolution,[status(thm)],[c_5,c_29])).

cnf(c_3818,plain,
    ( ~ v3_pre_topc(X0_49,sK5)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0_49,X1_49)
    | r1_tarski(X0_49,k1_tops_1(sK5,X1_49)) ),
    inference(subtyping,[status(esa)],[c_616])).

cnf(c_4286,plain,
    ( ~ v3_pre_topc(sK8,sK5)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(sK8,X0_49)
    | r1_tarski(sK8,k1_tops_1(sK5,X0_49)) ),
    inference(instantiation,[status(thm)],[c_3818])).

cnf(c_4288,plain,
    ( ~ v3_pre_topc(sK8,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK8,k1_tops_1(sK5,sK7))
    | ~ r1_tarski(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_4286])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3835,plain,
    ( ~ r1_tarski(X0_49,X1_49)
    | ~ r1_tarski(X2_49,X0_49)
    | r1_tarski(X2_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4091,plain,
    ( r1_tarski(X0_49,u1_struct_0(sK5))
    | ~ r1_tarski(X0_49,sK7)
    | ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3835])).

cnf(c_4208,plain,
    ( r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5))
    | ~ r1_tarski(k1_tops_1(sK5,sK7),sK7)
    | ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4091])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3834,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | ~ r1_tarski(X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4147,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0_49,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3834])).

cnf(c_4184,plain,
    ( m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4147])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3833,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | r1_tarski(X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4013,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3833])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v3_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_540,plain,
    ( sP1(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[status(thm)],[c_18,c_30])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | sP1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_540,c_29])).

cnf(c_545,plain,
    ( sP1(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_544])).

cnf(c_580,plain,
    ( sP0(X0,sK5)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(resolution,[status(thm)],[c_7,c_545])).

cnf(c_3820,plain,
    ( sP0(X0_49,sK5)
    | ~ v3_pre_topc(X0_49,sK5)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_580])).

cnf(c_4008,plain,
    ( sP0(k1_tops_1(sK5,X0_49),sK5)
    | ~ v3_pre_topc(k1_tops_1(sK5,X0_49),sK5)
    | ~ m1_subset_1(k1_tops_1(sK5,X0_49),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_3820])).

cnf(c_4010,plain,
    ( sP0(k1_tops_1(sK5,sK7),sK5)
    | ~ v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
    | ~ m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_4008])).

cnf(c_22,negated_conjecture,
    ( ~ m1_connsp_2(sK7,sK5,sK6)
    | ~ r2_hidden(sK6,X0)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_504,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[status(thm)],[c_19,c_31])).

cnf(c_508,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_30,c_29])).

cnf(c_794,plain,
    ( ~ r2_hidden(sK6,X0)
    | ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r1_tarski(X0,sK7) ),
    inference(resolution,[status(thm)],[c_22,c_508])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_798,plain,
    ( ~ r2_hidden(sK6,X0)
    | ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_794,c_28,c_27])).

cnf(c_3808,plain,
    ( ~ r2_hidden(sK6,X0_49)
    | ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ v3_pre_topc(X0_49,sK5)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0_49,sK7) ),
    inference(subtyping,[status(esa)],[c_798])).

cnf(c_3990,plain,
    ( ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
    | ~ m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(k1_tops_1(sK5,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_3808])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_636,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,X0),X0) ),
    inference(resolution,[status(thm)],[c_4,c_29])).

cnf(c_3817,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,X0_49),X0_49) ),
    inference(subtyping,[status(esa)],[c_636])).

cnf(c_3885,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_3817])).

cnf(c_3,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_557,plain,
    ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[status(thm)],[c_3,c_30])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(k1_tops_1(sK5,X0),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_29])).

cnf(c_562,plain,
    ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_561])).

cnf(c_3821,plain,
    ( v3_pre_topc(k1_tops_1(sK5,X0_49),sK5)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_562])).

cnf(c_3873,plain,
    ( v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_3821])).

cnf(c_23,negated_conjecture,
    ( m1_connsp_2(sK7,sK5,sK6)
    | r2_hidden(sK6,sK8) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_20,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_21,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_182,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_21])).

cnf(c_183,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_464,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[status(thm)],[c_183,c_31])).

cnf(c_468,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_30,c_29])).

cnf(c_781,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | r2_hidden(sK6,sK8)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_23,c_468])).

cnf(c_783,plain,
    ( r2_hidden(sK6,sK8)
    | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_28])).

cnf(c_784,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | r2_hidden(sK6,sK8) ),
    inference(renaming,[status(thm)],[c_783])).

cnf(c_24,negated_conjecture,
    ( m1_connsp_2(sK7,sK5,sK6)
    | r1_tarski(sK8,sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_767,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | r1_tarski(sK8,sK7) ),
    inference(resolution,[status(thm)],[c_24,c_468])).

cnf(c_769,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | r1_tarski(sK8,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_767,c_28])).

cnf(c_25,negated_conjecture,
    ( m1_connsp_2(sK7,sK5,sK6)
    | v3_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_753,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | v3_pre_topc(sK8,sK5)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_25,c_468])).

cnf(c_755,plain,
    ( v3_pre_topc(sK8,sK5)
    | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_28])).

cnf(c_756,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | v3_pre_topc(sK8,sK5) ),
    inference(renaming,[status(thm)],[c_755])).

cnf(c_26,negated_conjecture,
    ( m1_connsp_2(sK7,sK5,sK6)
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_739,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_26,c_468])).

cnf(c_741,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_28])).

cnf(c_742,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_741])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4620,c_4288,c_4208,c_4184,c_4013,c_4010,c_3990,c_3885,c_3873,c_784,c_769,c_756,c_742,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.42/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.42/1.01  
% 1.42/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.42/1.01  
% 1.42/1.01  ------  iProver source info
% 1.42/1.01  
% 1.42/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.42/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.42/1.01  git: non_committed_changes: false
% 1.42/1.01  git: last_make_outside_of_git: false
% 1.42/1.01  
% 1.42/1.01  ------ 
% 1.42/1.01  
% 1.42/1.01  ------ Input Options
% 1.42/1.01  
% 1.42/1.01  --out_options                           all
% 1.42/1.01  --tptp_safe_out                         true
% 1.42/1.01  --problem_path                          ""
% 1.42/1.01  --include_path                          ""
% 1.42/1.01  --clausifier                            res/vclausify_rel
% 1.42/1.01  --clausifier_options                    --mode clausify
% 1.42/1.01  --stdin                                 false
% 1.42/1.01  --stats_out                             all
% 1.42/1.01  
% 1.42/1.01  ------ General Options
% 1.42/1.01  
% 1.42/1.01  --fof                                   false
% 1.42/1.01  --time_out_real                         305.
% 1.42/1.01  --time_out_virtual                      -1.
% 1.42/1.01  --symbol_type_check                     false
% 1.42/1.01  --clausify_out                          false
% 1.42/1.01  --sig_cnt_out                           false
% 1.42/1.02  --trig_cnt_out                          false
% 1.42/1.02  --trig_cnt_out_tolerance                1.
% 1.42/1.02  --trig_cnt_out_sk_spl                   false
% 1.42/1.02  --abstr_cl_out                          false
% 1.42/1.02  
% 1.42/1.02  ------ Global Options
% 1.42/1.02  
% 1.42/1.02  --schedule                              default
% 1.42/1.02  --add_important_lit                     false
% 1.42/1.02  --prop_solver_per_cl                    1000
% 1.42/1.02  --min_unsat_core                        false
% 1.42/1.02  --soft_assumptions                      false
% 1.42/1.02  --soft_lemma_size                       3
% 1.42/1.02  --prop_impl_unit_size                   0
% 1.42/1.02  --prop_impl_unit                        []
% 1.42/1.02  --share_sel_clauses                     true
% 1.42/1.02  --reset_solvers                         false
% 1.42/1.02  --bc_imp_inh                            [conj_cone]
% 1.42/1.02  --conj_cone_tolerance                   3.
% 1.42/1.02  --extra_neg_conj                        none
% 1.42/1.02  --large_theory_mode                     true
% 1.42/1.02  --prolific_symb_bound                   200
% 1.42/1.02  --lt_threshold                          2000
% 1.42/1.02  --clause_weak_htbl                      true
% 1.42/1.02  --gc_record_bc_elim                     false
% 1.42/1.02  
% 1.42/1.02  ------ Preprocessing Options
% 1.42/1.02  
% 1.42/1.02  --preprocessing_flag                    true
% 1.42/1.02  --time_out_prep_mult                    0.1
% 1.42/1.02  --splitting_mode                        input
% 1.42/1.02  --splitting_grd                         true
% 1.42/1.02  --splitting_cvd                         false
% 1.42/1.02  --splitting_cvd_svl                     false
% 1.42/1.02  --splitting_nvd                         32
% 1.42/1.02  --sub_typing                            true
% 1.42/1.02  --prep_gs_sim                           true
% 1.42/1.02  --prep_unflatten                        true
% 1.42/1.02  --prep_res_sim                          true
% 1.42/1.02  --prep_upred                            true
% 1.42/1.02  --prep_sem_filter                       exhaustive
% 1.42/1.02  --prep_sem_filter_out                   false
% 1.42/1.02  --pred_elim                             true
% 1.42/1.02  --res_sim_input                         true
% 1.42/1.02  --eq_ax_congr_red                       true
% 1.42/1.02  --pure_diseq_elim                       true
% 1.42/1.02  --brand_transform                       false
% 1.42/1.02  --non_eq_to_eq                          false
% 1.42/1.02  --prep_def_merge                        true
% 1.42/1.02  --prep_def_merge_prop_impl              false
% 1.42/1.02  --prep_def_merge_mbd                    true
% 1.42/1.02  --prep_def_merge_tr_red                 false
% 1.42/1.02  --prep_def_merge_tr_cl                  false
% 1.42/1.02  --smt_preprocessing                     true
% 1.42/1.02  --smt_ac_axioms                         fast
% 1.42/1.02  --preprocessed_out                      false
% 1.42/1.02  --preprocessed_stats                    false
% 1.42/1.02  
% 1.42/1.02  ------ Abstraction refinement Options
% 1.42/1.02  
% 1.42/1.02  --abstr_ref                             []
% 1.42/1.02  --abstr_ref_prep                        false
% 1.42/1.02  --abstr_ref_until_sat                   false
% 1.42/1.02  --abstr_ref_sig_restrict                funpre
% 1.42/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.42/1.02  --abstr_ref_under                       []
% 1.42/1.02  
% 1.42/1.02  ------ SAT Options
% 1.42/1.02  
% 1.42/1.02  --sat_mode                              false
% 1.42/1.02  --sat_fm_restart_options                ""
% 1.42/1.02  --sat_gr_def                            false
% 1.42/1.02  --sat_epr_types                         true
% 1.42/1.02  --sat_non_cyclic_types                  false
% 1.42/1.02  --sat_finite_models                     false
% 1.42/1.02  --sat_fm_lemmas                         false
% 1.42/1.02  --sat_fm_prep                           false
% 1.42/1.02  --sat_fm_uc_incr                        true
% 1.42/1.02  --sat_out_model                         small
% 1.42/1.02  --sat_out_clauses                       false
% 1.42/1.02  
% 1.42/1.02  ------ QBF Options
% 1.42/1.02  
% 1.42/1.02  --qbf_mode                              false
% 1.42/1.02  --qbf_elim_univ                         false
% 1.42/1.02  --qbf_dom_inst                          none
% 1.42/1.02  --qbf_dom_pre_inst                      false
% 1.42/1.02  --qbf_sk_in                             false
% 1.42/1.02  --qbf_pred_elim                         true
% 1.42/1.02  --qbf_split                             512
% 1.42/1.02  
% 1.42/1.02  ------ BMC1 Options
% 1.42/1.02  
% 1.42/1.02  --bmc1_incremental                      false
% 1.42/1.02  --bmc1_axioms                           reachable_all
% 1.42/1.02  --bmc1_min_bound                        0
% 1.42/1.02  --bmc1_max_bound                        -1
% 1.42/1.02  --bmc1_max_bound_default                -1
% 1.42/1.02  --bmc1_symbol_reachability              true
% 1.42/1.02  --bmc1_property_lemmas                  false
% 1.42/1.02  --bmc1_k_induction                      false
% 1.42/1.02  --bmc1_non_equiv_states                 false
% 1.42/1.02  --bmc1_deadlock                         false
% 1.42/1.02  --bmc1_ucm                              false
% 1.42/1.02  --bmc1_add_unsat_core                   none
% 1.42/1.02  --bmc1_unsat_core_children              false
% 1.42/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.42/1.02  --bmc1_out_stat                         full
% 1.42/1.02  --bmc1_ground_init                      false
% 1.42/1.02  --bmc1_pre_inst_next_state              false
% 1.42/1.02  --bmc1_pre_inst_state                   false
% 1.42/1.02  --bmc1_pre_inst_reach_state             false
% 1.42/1.02  --bmc1_out_unsat_core                   false
% 1.42/1.02  --bmc1_aig_witness_out                  false
% 1.42/1.02  --bmc1_verbose                          false
% 1.42/1.02  --bmc1_dump_clauses_tptp                false
% 1.42/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.42/1.02  --bmc1_dump_file                        -
% 1.42/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.42/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.42/1.02  --bmc1_ucm_extend_mode                  1
% 1.42/1.02  --bmc1_ucm_init_mode                    2
% 1.42/1.02  --bmc1_ucm_cone_mode                    none
% 1.42/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.42/1.02  --bmc1_ucm_relax_model                  4
% 1.42/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.42/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.42/1.02  --bmc1_ucm_layered_model                none
% 1.42/1.02  --bmc1_ucm_max_lemma_size               10
% 1.42/1.02  
% 1.42/1.02  ------ AIG Options
% 1.42/1.02  
% 1.42/1.02  --aig_mode                              false
% 1.42/1.02  
% 1.42/1.02  ------ Instantiation Options
% 1.42/1.02  
% 1.42/1.02  --instantiation_flag                    true
% 1.42/1.02  --inst_sos_flag                         false
% 1.42/1.02  --inst_sos_phase                        true
% 1.42/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.42/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.42/1.02  --inst_lit_sel_side                     num_symb
% 1.42/1.02  --inst_solver_per_active                1400
% 1.42/1.02  --inst_solver_calls_frac                1.
% 1.42/1.02  --inst_passive_queue_type               priority_queues
% 1.42/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.42/1.02  --inst_passive_queues_freq              [25;2]
% 1.42/1.02  --inst_dismatching                      true
% 1.42/1.02  --inst_eager_unprocessed_to_passive     true
% 1.42/1.02  --inst_prop_sim_given                   true
% 1.42/1.02  --inst_prop_sim_new                     false
% 1.42/1.02  --inst_subs_new                         false
% 1.42/1.02  --inst_eq_res_simp                      false
% 1.42/1.02  --inst_subs_given                       false
% 1.42/1.02  --inst_orphan_elimination               true
% 1.42/1.02  --inst_learning_loop_flag               true
% 1.42/1.02  --inst_learning_start                   3000
% 1.42/1.02  --inst_learning_factor                  2
% 1.42/1.02  --inst_start_prop_sim_after_learn       3
% 1.42/1.02  --inst_sel_renew                        solver
% 1.42/1.02  --inst_lit_activity_flag                true
% 1.42/1.02  --inst_restr_to_given                   false
% 1.42/1.02  --inst_activity_threshold               500
% 1.42/1.02  --inst_out_proof                        true
% 1.42/1.02  
% 1.42/1.02  ------ Resolution Options
% 1.42/1.02  
% 1.42/1.02  --resolution_flag                       true
% 1.42/1.02  --res_lit_sel                           adaptive
% 1.42/1.02  --res_lit_sel_side                      none
% 1.42/1.02  --res_ordering                          kbo
% 1.42/1.02  --res_to_prop_solver                    active
% 1.42/1.02  --res_prop_simpl_new                    false
% 1.42/1.02  --res_prop_simpl_given                  true
% 1.42/1.02  --res_passive_queue_type                priority_queues
% 1.42/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.42/1.02  --res_passive_queues_freq               [15;5]
% 1.42/1.02  --res_forward_subs                      full
% 1.42/1.02  --res_backward_subs                     full
% 1.42/1.02  --res_forward_subs_resolution           true
% 1.42/1.02  --res_backward_subs_resolution          true
% 1.42/1.02  --res_orphan_elimination                true
% 1.42/1.02  --res_time_limit                        2.
% 1.42/1.02  --res_out_proof                         true
% 1.42/1.02  
% 1.42/1.02  ------ Superposition Options
% 1.42/1.02  
% 1.42/1.02  --superposition_flag                    true
% 1.42/1.02  --sup_passive_queue_type                priority_queues
% 1.42/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.42/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.42/1.02  --demod_completeness_check              fast
% 1.42/1.02  --demod_use_ground                      true
% 1.42/1.02  --sup_to_prop_solver                    passive
% 1.42/1.02  --sup_prop_simpl_new                    true
% 1.42/1.02  --sup_prop_simpl_given                  true
% 1.42/1.02  --sup_fun_splitting                     false
% 1.42/1.02  --sup_smt_interval                      50000
% 1.42/1.02  
% 1.42/1.02  ------ Superposition Simplification Setup
% 1.42/1.02  
% 1.42/1.02  --sup_indices_passive                   []
% 1.42/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.42/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.02  --sup_full_bw                           [BwDemod]
% 1.42/1.02  --sup_immed_triv                        [TrivRules]
% 1.42/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.42/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.02  --sup_immed_bw_main                     []
% 1.42/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.42/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.42/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.42/1.02  
% 1.42/1.02  ------ Combination Options
% 1.42/1.02  
% 1.42/1.02  --comb_res_mult                         3
% 1.42/1.02  --comb_sup_mult                         2
% 1.42/1.02  --comb_inst_mult                        10
% 1.42/1.02  
% 1.42/1.02  ------ Debug Options
% 1.42/1.02  
% 1.42/1.02  --dbg_backtrace                         false
% 1.42/1.02  --dbg_dump_prop_clauses                 false
% 1.42/1.02  --dbg_dump_prop_clauses_file            -
% 1.42/1.02  --dbg_out_stat                          false
% 1.42/1.02  ------ Parsing...
% 1.42/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.42/1.02  
% 1.42/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.42/1.02  
% 1.42/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.42/1.02  ------ Proving...
% 1.42/1.02  ------ Problem Properties 
% 1.42/1.02  
% 1.42/1.02  
% 1.42/1.02  clauses                                 28
% 1.42/1.02  conjectures                             1
% 1.42/1.02  EPR                                     1
% 1.42/1.02  Horn                                    20
% 1.42/1.02  unary                                   1
% 1.42/1.02  binary                                  8
% 1.42/1.02  lits                                    92
% 1.42/1.02  lits eq                                 0
% 1.42/1.02  fd_pure                                 0
% 1.42/1.02  fd_pseudo                               0
% 1.42/1.02  fd_cond                                 0
% 1.42/1.02  fd_pseudo_cond                          0
% 1.42/1.02  AC symbols                              0
% 1.42/1.02  
% 1.42/1.02  ------ Schedule dynamic 5 is on 
% 1.42/1.02  
% 1.42/1.02  ------ no equalities: superposition off 
% 1.42/1.02  
% 1.42/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.42/1.02  
% 1.42/1.02  
% 1.42/1.02  ------ 
% 1.42/1.02  Current options:
% 1.42/1.02  ------ 
% 1.42/1.02  
% 1.42/1.02  ------ Input Options
% 1.42/1.02  
% 1.42/1.02  --out_options                           all
% 1.42/1.02  --tptp_safe_out                         true
% 1.42/1.02  --problem_path                          ""
% 1.42/1.02  --include_path                          ""
% 1.42/1.02  --clausifier                            res/vclausify_rel
% 1.42/1.02  --clausifier_options                    --mode clausify
% 1.42/1.02  --stdin                                 false
% 1.42/1.02  --stats_out                             all
% 1.42/1.02  
% 1.42/1.02  ------ General Options
% 1.42/1.02  
% 1.42/1.02  --fof                                   false
% 1.42/1.02  --time_out_real                         305.
% 1.42/1.02  --time_out_virtual                      -1.
% 1.42/1.02  --symbol_type_check                     false
% 1.42/1.02  --clausify_out                          false
% 1.42/1.02  --sig_cnt_out                           false
% 1.42/1.02  --trig_cnt_out                          false
% 1.42/1.02  --trig_cnt_out_tolerance                1.
% 1.42/1.02  --trig_cnt_out_sk_spl                   false
% 1.42/1.02  --abstr_cl_out                          false
% 1.42/1.02  
% 1.42/1.02  ------ Global Options
% 1.42/1.02  
% 1.42/1.02  --schedule                              default
% 1.42/1.02  --add_important_lit                     false
% 1.42/1.02  --prop_solver_per_cl                    1000
% 1.42/1.02  --min_unsat_core                        false
% 1.42/1.02  --soft_assumptions                      false
% 1.42/1.02  --soft_lemma_size                       3
% 1.42/1.02  --prop_impl_unit_size                   0
% 1.42/1.02  --prop_impl_unit                        []
% 1.42/1.02  --share_sel_clauses                     true
% 1.42/1.02  --reset_solvers                         false
% 1.42/1.02  --bc_imp_inh                            [conj_cone]
% 1.42/1.02  --conj_cone_tolerance                   3.
% 1.42/1.02  --extra_neg_conj                        none
% 1.42/1.02  --large_theory_mode                     true
% 1.42/1.02  --prolific_symb_bound                   200
% 1.42/1.02  --lt_threshold                          2000
% 1.42/1.02  --clause_weak_htbl                      true
% 1.42/1.02  --gc_record_bc_elim                     false
% 1.42/1.02  
% 1.42/1.02  ------ Preprocessing Options
% 1.42/1.02  
% 1.42/1.02  --preprocessing_flag                    true
% 1.42/1.02  --time_out_prep_mult                    0.1
% 1.42/1.02  --splitting_mode                        input
% 1.42/1.02  --splitting_grd                         true
% 1.42/1.02  --splitting_cvd                         false
% 1.42/1.02  --splitting_cvd_svl                     false
% 1.42/1.02  --splitting_nvd                         32
% 1.42/1.02  --sub_typing                            true
% 1.42/1.02  --prep_gs_sim                           true
% 1.42/1.02  --prep_unflatten                        true
% 1.42/1.02  --prep_res_sim                          true
% 1.42/1.02  --prep_upred                            true
% 1.42/1.02  --prep_sem_filter                       exhaustive
% 1.42/1.02  --prep_sem_filter_out                   false
% 1.42/1.02  --pred_elim                             true
% 1.42/1.02  --res_sim_input                         true
% 1.42/1.02  --eq_ax_congr_red                       true
% 1.42/1.02  --pure_diseq_elim                       true
% 1.42/1.02  --brand_transform                       false
% 1.42/1.02  --non_eq_to_eq                          false
% 1.42/1.02  --prep_def_merge                        true
% 1.42/1.02  --prep_def_merge_prop_impl              false
% 1.42/1.02  --prep_def_merge_mbd                    true
% 1.42/1.02  --prep_def_merge_tr_red                 false
% 1.42/1.02  --prep_def_merge_tr_cl                  false
% 1.42/1.02  --smt_preprocessing                     true
% 1.42/1.02  --smt_ac_axioms                         fast
% 1.42/1.02  --preprocessed_out                      false
% 1.42/1.02  --preprocessed_stats                    false
% 1.42/1.02  
% 1.42/1.02  ------ Abstraction refinement Options
% 1.42/1.02  
% 1.42/1.02  --abstr_ref                             []
% 1.42/1.02  --abstr_ref_prep                        false
% 1.42/1.02  --abstr_ref_until_sat                   false
% 1.42/1.02  --abstr_ref_sig_restrict                funpre
% 1.42/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.42/1.02  --abstr_ref_under                       []
% 1.42/1.02  
% 1.42/1.02  ------ SAT Options
% 1.42/1.02  
% 1.42/1.02  --sat_mode                              false
% 1.42/1.02  --sat_fm_restart_options                ""
% 1.42/1.02  --sat_gr_def                            false
% 1.42/1.02  --sat_epr_types                         true
% 1.42/1.02  --sat_non_cyclic_types                  false
% 1.42/1.02  --sat_finite_models                     false
% 1.42/1.02  --sat_fm_lemmas                         false
% 1.42/1.02  --sat_fm_prep                           false
% 1.42/1.02  --sat_fm_uc_incr                        true
% 1.42/1.02  --sat_out_model                         small
% 1.42/1.02  --sat_out_clauses                       false
% 1.42/1.02  
% 1.42/1.02  ------ QBF Options
% 1.42/1.02  
% 1.42/1.02  --qbf_mode                              false
% 1.42/1.02  --qbf_elim_univ                         false
% 1.42/1.02  --qbf_dom_inst                          none
% 1.42/1.02  --qbf_dom_pre_inst                      false
% 1.42/1.02  --qbf_sk_in                             false
% 1.42/1.02  --qbf_pred_elim                         true
% 1.42/1.02  --qbf_split                             512
% 1.42/1.02  
% 1.42/1.02  ------ BMC1 Options
% 1.42/1.02  
% 1.42/1.02  --bmc1_incremental                      false
% 1.42/1.02  --bmc1_axioms                           reachable_all
% 1.42/1.02  --bmc1_min_bound                        0
% 1.42/1.02  --bmc1_max_bound                        -1
% 1.42/1.02  --bmc1_max_bound_default                -1
% 1.42/1.02  --bmc1_symbol_reachability              true
% 1.42/1.02  --bmc1_property_lemmas                  false
% 1.42/1.02  --bmc1_k_induction                      false
% 1.42/1.02  --bmc1_non_equiv_states                 false
% 1.42/1.02  --bmc1_deadlock                         false
% 1.42/1.02  --bmc1_ucm                              false
% 1.42/1.02  --bmc1_add_unsat_core                   none
% 1.42/1.02  --bmc1_unsat_core_children              false
% 1.42/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.42/1.02  --bmc1_out_stat                         full
% 1.42/1.02  --bmc1_ground_init                      false
% 1.42/1.02  --bmc1_pre_inst_next_state              false
% 1.42/1.02  --bmc1_pre_inst_state                   false
% 1.42/1.02  --bmc1_pre_inst_reach_state             false
% 1.42/1.02  --bmc1_out_unsat_core                   false
% 1.42/1.02  --bmc1_aig_witness_out                  false
% 1.42/1.02  --bmc1_verbose                          false
% 1.42/1.02  --bmc1_dump_clauses_tptp                false
% 1.42/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.42/1.02  --bmc1_dump_file                        -
% 1.42/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.42/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.42/1.02  --bmc1_ucm_extend_mode                  1
% 1.42/1.02  --bmc1_ucm_init_mode                    2
% 1.42/1.02  --bmc1_ucm_cone_mode                    none
% 1.42/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.42/1.02  --bmc1_ucm_relax_model                  4
% 1.42/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.42/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.42/1.02  --bmc1_ucm_layered_model                none
% 1.42/1.02  --bmc1_ucm_max_lemma_size               10
% 1.42/1.02  
% 1.42/1.02  ------ AIG Options
% 1.42/1.02  
% 1.42/1.02  --aig_mode                              false
% 1.42/1.02  
% 1.42/1.02  ------ Instantiation Options
% 1.42/1.02  
% 1.42/1.02  --instantiation_flag                    true
% 1.42/1.02  --inst_sos_flag                         false
% 1.42/1.02  --inst_sos_phase                        true
% 1.42/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.42/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.42/1.02  --inst_lit_sel_side                     none
% 1.42/1.02  --inst_solver_per_active                1400
% 1.42/1.02  --inst_solver_calls_frac                1.
% 1.42/1.02  --inst_passive_queue_type               priority_queues
% 1.42/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.42/1.02  --inst_passive_queues_freq              [25;2]
% 1.42/1.02  --inst_dismatching                      true
% 1.42/1.02  --inst_eager_unprocessed_to_passive     true
% 1.42/1.02  --inst_prop_sim_given                   true
% 1.42/1.02  --inst_prop_sim_new                     false
% 1.42/1.02  --inst_subs_new                         false
% 1.42/1.02  --inst_eq_res_simp                      false
% 1.42/1.02  --inst_subs_given                       false
% 1.42/1.02  --inst_orphan_elimination               true
% 1.42/1.02  --inst_learning_loop_flag               true
% 1.42/1.02  --inst_learning_start                   3000
% 1.42/1.02  --inst_learning_factor                  2
% 1.42/1.02  --inst_start_prop_sim_after_learn       3
% 1.42/1.02  --inst_sel_renew                        solver
% 1.42/1.02  --inst_lit_activity_flag                true
% 1.42/1.02  --inst_restr_to_given                   false
% 1.42/1.02  --inst_activity_threshold               500
% 1.42/1.02  --inst_out_proof                        true
% 1.42/1.02  
% 1.42/1.02  ------ Resolution Options
% 1.42/1.02  
% 1.42/1.02  --resolution_flag                       false
% 1.42/1.02  --res_lit_sel                           adaptive
% 1.42/1.02  --res_lit_sel_side                      none
% 1.42/1.02  --res_ordering                          kbo
% 1.42/1.02  --res_to_prop_solver                    active
% 1.42/1.02  --res_prop_simpl_new                    false
% 1.42/1.02  --res_prop_simpl_given                  true
% 1.42/1.02  --res_passive_queue_type                priority_queues
% 1.42/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.42/1.02  --res_passive_queues_freq               [15;5]
% 1.42/1.02  --res_forward_subs                      full
% 1.42/1.02  --res_backward_subs                     full
% 1.42/1.02  --res_forward_subs_resolution           true
% 1.42/1.02  --res_backward_subs_resolution          true
% 1.42/1.02  --res_orphan_elimination                true
% 1.42/1.02  --res_time_limit                        2.
% 1.42/1.02  --res_out_proof                         true
% 1.42/1.02  
% 1.42/1.02  ------ Superposition Options
% 1.42/1.02  
% 1.42/1.02  --superposition_flag                    false
% 1.42/1.02  --sup_passive_queue_type                priority_queues
% 1.42/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.42/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.42/1.02  --demod_completeness_check              fast
% 1.42/1.02  --demod_use_ground                      true
% 1.42/1.02  --sup_to_prop_solver                    passive
% 1.42/1.02  --sup_prop_simpl_new                    true
% 1.42/1.02  --sup_prop_simpl_given                  true
% 1.42/1.02  --sup_fun_splitting                     false
% 1.42/1.02  --sup_smt_interval                      50000
% 1.42/1.02  
% 1.42/1.02  ------ Superposition Simplification Setup
% 1.42/1.02  
% 1.42/1.02  --sup_indices_passive                   []
% 1.42/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.42/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.02  --sup_full_bw                           [BwDemod]
% 1.42/1.02  --sup_immed_triv                        [TrivRules]
% 1.42/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.42/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.02  --sup_immed_bw_main                     []
% 1.42/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.42/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.42/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.42/1.02  
% 1.42/1.02  ------ Combination Options
% 1.42/1.02  
% 1.42/1.02  --comb_res_mult                         3
% 1.42/1.02  --comb_sup_mult                         2
% 1.42/1.02  --comb_inst_mult                        10
% 1.42/1.02  
% 1.42/1.02  ------ Debug Options
% 1.42/1.02  
% 1.42/1.02  --dbg_backtrace                         false
% 1.42/1.02  --dbg_dump_prop_clauses                 false
% 1.42/1.02  --dbg_dump_prop_clauses_file            -
% 1.42/1.02  --dbg_out_stat                          false
% 1.42/1.02  
% 1.42/1.02  
% 1.42/1.02  
% 1.42/1.02  
% 1.42/1.02  ------ Proving...
% 1.42/1.02  
% 1.42/1.02  
% 1.42/1.02  % SZS status Theorem for theBenchmark.p
% 1.42/1.02  
% 1.42/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.42/1.02  
% 1.42/1.02  fof(f26,plain,(
% 1.42/1.02    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.42/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.42/1.02  
% 1.42/1.02  fof(f31,plain,(
% 1.42/1.02    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1))) | ~sP0(X1,X0)))),
% 1.42/1.02    inference(nnf_transformation,[],[f26])).
% 1.42/1.02  
% 1.42/1.02  fof(f32,plain,(
% 1.42/1.02    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 1.42/1.02    inference(rectify,[],[f31])).
% 1.42/1.02  
% 1.42/1.02  fof(f35,plain,(
% 1.42/1.02    ! [X5,X1,X0] : (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X5,sK4(X0,X1,X5)) & r1_tarski(sK4(X0,X1,X5),X0) & v3_pre_topc(sK4(X0,X1,X5),X1) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.42/1.02    introduced(choice_axiom,[])).
% 1.42/1.02  
% 1.42/1.02  fof(f34,plain,(
% 1.42/1.02    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X2,sK3(X0,X1)) & r1_tarski(sK3(X0,X1),X0) & v3_pre_topc(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 1.42/1.02    introduced(choice_axiom,[])).
% 1.42/1.02  
% 1.42/1.02  fof(f33,plain,(
% 1.42/1.02    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0))) => ((! [X3] : (~r2_hidden(sK2(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),X0)) & (? [X4] : (r2_hidden(sK2(X0,X1),X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),X0))))),
% 1.42/1.02    introduced(choice_axiom,[])).
% 1.42/1.02  
% 1.42/1.02  fof(f36,plain,(
% 1.42/1.02    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (~r2_hidden(sK2(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),X0)) & ((r2_hidden(sK2(X0,X1),sK3(X0,X1)) & r1_tarski(sK3(X0,X1),X0) & v3_pre_topc(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((r2_hidden(X5,sK4(X0,X1,X5)) & r1_tarski(sK4(X0,X1,X5),X0) & v3_pre_topc(sK4(X0,X1,X5),X1) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 1.42/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).
% 1.42/1.02  
% 1.42/1.02  fof(f58,plain,(
% 1.42/1.02    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X0) | ~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f36])).
% 1.42/1.02  
% 1.42/1.02  fof(f5,axiom,(
% 1.42/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.42/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.02  
% 1.42/1.02  fof(f16,plain,(
% 1.42/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/1.02    inference(ennf_transformation,[],[f5])).
% 1.42/1.02  
% 1.42/1.02  fof(f17,plain,(
% 1.42/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/1.02    inference(flattening,[],[f16])).
% 1.42/1.02  
% 1.42/1.02  fof(f51,plain,(
% 1.42/1.02    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f17])).
% 1.42/1.02  
% 1.42/1.02  fof(f9,conjecture,(
% 1.42/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.42/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.02  
% 1.42/1.02  fof(f10,negated_conjecture,(
% 1.42/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.42/1.02    inference(negated_conjecture,[],[f9])).
% 1.42/1.02  
% 1.42/1.02  fof(f24,plain,(
% 1.42/1.02    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.42/1.02    inference(ennf_transformation,[],[f10])).
% 1.42/1.02  
% 1.42/1.02  fof(f25,plain,(
% 1.42/1.02    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.42/1.02    inference(flattening,[],[f24])).
% 1.42/1.02  
% 1.42/1.02  fof(f38,plain,(
% 1.42/1.02    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.42/1.02    inference(nnf_transformation,[],[f25])).
% 1.42/1.02  
% 1.42/1.02  fof(f39,plain,(
% 1.42/1.02    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.42/1.02    inference(flattening,[],[f38])).
% 1.42/1.02  
% 1.42/1.02  fof(f40,plain,(
% 1.42/1.02    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.42/1.02    inference(rectify,[],[f39])).
% 1.42/1.02  
% 1.42/1.02  fof(f44,plain,(
% 1.42/1.02    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK8) & r1_tarski(sK8,X2) & v3_pre_topc(sK8,X0) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.42/1.02    introduced(choice_axiom,[])).
% 1.42/1.02  
% 1.42/1.02  fof(f43,plain,(
% 1.42/1.02    ( ! [X0,X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,sK7) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(sK7,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,sK7) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(sK7,X0,X1)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.42/1.02    introduced(choice_axiom,[])).
% 1.42/1.02  
% 1.42/1.02  fof(f42,plain,(
% 1.42/1.02    ( ! [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK6,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,sK6)) & (? [X4] : (r2_hidden(sK6,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,sK6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 1.42/1.02    introduced(choice_axiom,[])).
% 1.42/1.02  
% 1.42/1.02  fof(f41,plain,(
% 1.42/1.02    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK5) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))) | ~m1_connsp_2(X2,sK5,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK5) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK5)))) | m1_connsp_2(X2,sK5,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 1.42/1.02    introduced(choice_axiom,[])).
% 1.42/1.02  
% 1.42/1.02  fof(f45,plain,(
% 1.42/1.02    (((! [X3] : (~r2_hidden(sK6,X3) | ~r1_tarski(X3,sK7) | ~v3_pre_topc(X3,sK5) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))) | ~m1_connsp_2(sK7,sK5,sK6)) & ((r2_hidden(sK6,sK8) & r1_tarski(sK8,sK7) & v3_pre_topc(sK8,sK5) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))) | m1_connsp_2(sK7,sK5,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 1.42/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f40,f44,f43,f42,f41])).
% 1.42/1.02  
% 1.42/1.02  fof(f70,plain,(
% 1.42/1.02    l1_pre_topc(sK5)),
% 1.42/1.02    inference(cnf_transformation,[],[f45])).
% 1.42/1.02  
% 1.42/1.02  fof(f1,axiom,(
% 1.42/1.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.42/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.02  
% 1.42/1.02  fof(f11,plain,(
% 1.42/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.42/1.02    inference(ennf_transformation,[],[f1])).
% 1.42/1.02  
% 1.42/1.02  fof(f12,plain,(
% 1.42/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.42/1.02    inference(flattening,[],[f11])).
% 1.42/1.02  
% 1.42/1.02  fof(f46,plain,(
% 1.42/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f12])).
% 1.42/1.02  
% 1.42/1.02  fof(f2,axiom,(
% 1.42/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.42/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.02  
% 1.42/1.02  fof(f29,plain,(
% 1.42/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.42/1.02    inference(nnf_transformation,[],[f2])).
% 1.42/1.02  
% 1.42/1.02  fof(f48,plain,(
% 1.42/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f29])).
% 1.42/1.02  
% 1.42/1.02  fof(f47,plain,(
% 1.42/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.42/1.02    inference(cnf_transformation,[],[f29])).
% 1.42/1.02  
% 1.42/1.02  fof(f27,plain,(
% 1.42/1.02    ! [X0,X1] : ((v3_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.42/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.42/1.02  
% 1.42/1.02  fof(f30,plain,(
% 1.42/1.02    ! [X0,X1] : (((v3_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 1.42/1.02    inference(nnf_transformation,[],[f27])).
% 1.42/1.02  
% 1.42/1.02  fof(f52,plain,(
% 1.42/1.02    ( ! [X0,X1] : (sP0(X1,X0) | ~v3_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f30])).
% 1.42/1.02  
% 1.42/1.02  fof(f6,axiom,(
% 1.42/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.42/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.02  
% 1.42/1.02  fof(f18,plain,(
% 1.42/1.02    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/1.02    inference(ennf_transformation,[],[f6])).
% 1.42/1.02  
% 1.42/1.02  fof(f19,plain,(
% 1.42/1.02    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/1.02    inference(flattening,[],[f18])).
% 1.42/1.02  
% 1.42/1.02  fof(f28,plain,(
% 1.42/1.02    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/1.02    inference(definition_folding,[],[f19,f27,f26])).
% 1.42/1.02  
% 1.42/1.02  fof(f64,plain,(
% 1.42/1.02    ( ! [X0,X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f28])).
% 1.42/1.02  
% 1.42/1.02  fof(f69,plain,(
% 1.42/1.02    v2_pre_topc(sK5)),
% 1.42/1.02    inference(cnf_transformation,[],[f45])).
% 1.42/1.02  
% 1.42/1.02  fof(f77,plain,(
% 1.42/1.02    ( ! [X3] : (~r2_hidden(sK6,X3) | ~r1_tarski(X3,sK7) | ~v3_pre_topc(X3,sK5) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_connsp_2(sK7,sK5,sK6)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f45])).
% 1.42/1.02  
% 1.42/1.02  fof(f7,axiom,(
% 1.42/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.42/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.02  
% 1.42/1.02  fof(f20,plain,(
% 1.42/1.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/1.02    inference(ennf_transformation,[],[f7])).
% 1.42/1.02  
% 1.42/1.02  fof(f21,plain,(
% 1.42/1.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/1.02    inference(flattening,[],[f20])).
% 1.42/1.02  
% 1.42/1.02  fof(f37,plain,(
% 1.42/1.02    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/1.02    inference(nnf_transformation,[],[f21])).
% 1.42/1.02  
% 1.42/1.02  fof(f66,plain,(
% 1.42/1.02    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f37])).
% 1.42/1.02  
% 1.42/1.02  fof(f68,plain,(
% 1.42/1.02    ~v2_struct_0(sK5)),
% 1.42/1.02    inference(cnf_transformation,[],[f45])).
% 1.42/1.02  
% 1.42/1.02  fof(f71,plain,(
% 1.42/1.02    m1_subset_1(sK6,u1_struct_0(sK5))),
% 1.42/1.02    inference(cnf_transformation,[],[f45])).
% 1.42/1.02  
% 1.42/1.02  fof(f72,plain,(
% 1.42/1.02    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))),
% 1.42/1.02    inference(cnf_transformation,[],[f45])).
% 1.42/1.02  
% 1.42/1.02  fof(f4,axiom,(
% 1.42/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.42/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.02  
% 1.42/1.02  fof(f15,plain,(
% 1.42/1.02    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/1.02    inference(ennf_transformation,[],[f4])).
% 1.42/1.02  
% 1.42/1.02  fof(f50,plain,(
% 1.42/1.02    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f15])).
% 1.42/1.02  
% 1.42/1.02  fof(f3,axiom,(
% 1.42/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.42/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.02  
% 1.42/1.02  fof(f13,plain,(
% 1.42/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/1.02    inference(ennf_transformation,[],[f3])).
% 1.42/1.02  
% 1.42/1.02  fof(f14,plain,(
% 1.42/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/1.02    inference(flattening,[],[f13])).
% 1.42/1.02  
% 1.42/1.02  fof(f49,plain,(
% 1.42/1.02    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f14])).
% 1.42/1.02  
% 1.42/1.02  fof(f76,plain,(
% 1.42/1.02    r2_hidden(sK6,sK8) | m1_connsp_2(sK7,sK5,sK6)),
% 1.42/1.02    inference(cnf_transformation,[],[f45])).
% 1.42/1.02  
% 1.42/1.02  fof(f65,plain,(
% 1.42/1.02    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f37])).
% 1.42/1.02  
% 1.42/1.02  fof(f8,axiom,(
% 1.42/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.42/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.02  
% 1.42/1.02  fof(f22,plain,(
% 1.42/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/1.02    inference(ennf_transformation,[],[f8])).
% 1.42/1.02  
% 1.42/1.02  fof(f23,plain,(
% 1.42/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/1.02    inference(flattening,[],[f22])).
% 1.42/1.02  
% 1.42/1.02  fof(f67,plain,(
% 1.42/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/1.02    inference(cnf_transformation,[],[f23])).
% 1.42/1.02  
% 1.42/1.02  fof(f75,plain,(
% 1.42/1.02    r1_tarski(sK8,sK7) | m1_connsp_2(sK7,sK5,sK6)),
% 1.42/1.02    inference(cnf_transformation,[],[f45])).
% 1.42/1.02  
% 1.42/1.02  fof(f74,plain,(
% 1.42/1.02    v3_pre_topc(sK8,sK5) | m1_connsp_2(sK7,sK5,sK6)),
% 1.42/1.02    inference(cnf_transformation,[],[f45])).
% 1.42/1.02  
% 1.42/1.02  fof(f73,plain,(
% 1.42/1.02    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) | m1_connsp_2(sK7,sK5,sK6)),
% 1.42/1.02    inference(cnf_transformation,[],[f45])).
% 1.42/1.02  
% 1.42/1.02  cnf(c_13,plain,
% 1.42/1.02      ( ~ r2_hidden(X0,X1)
% 1.42/1.02      | r2_hidden(X0,X2)
% 1.42/1.02      | ~ sP0(X2,X3)
% 1.42/1.02      | ~ v3_pre_topc(X1,X3)
% 1.42/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
% 1.42/1.02      | ~ r1_tarski(X1,X2) ),
% 1.42/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3827,plain,
% 1.42/1.02      ( ~ r2_hidden(X0_48,X0_49)
% 1.42/1.02      | r2_hidden(X0_48,X1_49)
% 1.42/1.02      | ~ sP0(X1_49,X0_50)
% 1.42/1.02      | ~ v3_pre_topc(X0_49,X0_50)
% 1.42/1.02      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(X0_50)))
% 1.42/1.02      | ~ r1_tarski(X0_49,X1_49) ),
% 1.42/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4252,plain,
% 1.42/1.02      ( r2_hidden(sK6,X0_49)
% 1.42/1.02      | ~ r2_hidden(sK6,sK8)
% 1.42/1.02      | ~ sP0(X0_49,X0_50)
% 1.42/1.02      | ~ v3_pre_topc(sK8,X0_50)
% 1.42/1.02      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0_50)))
% 1.42/1.02      | ~ r1_tarski(sK8,X0_49) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_3827]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4618,plain,
% 1.42/1.02      ( r2_hidden(sK6,k1_tops_1(sK5,X0_49))
% 1.42/1.02      | ~ r2_hidden(sK6,sK8)
% 1.42/1.02      | ~ sP0(k1_tops_1(sK5,X0_49),sK5)
% 1.42/1.02      | ~ v3_pre_topc(sK8,sK5)
% 1.42/1.02      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(sK8,k1_tops_1(sK5,X0_49)) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_4252]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4620,plain,
% 1.42/1.02      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 1.42/1.02      | ~ r2_hidden(sK6,sK8)
% 1.42/1.02      | ~ sP0(k1_tops_1(sK5,sK7),sK5)
% 1.42/1.02      | ~ v3_pre_topc(sK8,sK5)
% 1.42/1.02      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(sK8,k1_tops_1(sK5,sK7)) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_4618]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_5,plain,
% 1.42/1.02      ( ~ v3_pre_topc(X0,X1)
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.42/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.42/1.02      | ~ r1_tarski(X0,X2)
% 1.42/1.02      | r1_tarski(X0,k1_tops_1(X1,X2))
% 1.42/1.02      | ~ l1_pre_topc(X1) ),
% 1.42/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_29,negated_conjecture,
% 1.42/1.02      ( l1_pre_topc(sK5) ),
% 1.42/1.02      inference(cnf_transformation,[],[f70]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_616,plain,
% 1.42/1.02      ( ~ v3_pre_topc(X0,sK5)
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(X0,X1)
% 1.42/1.02      | r1_tarski(X0,k1_tops_1(sK5,X1)) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_5,c_29]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3818,plain,
% 1.42/1.02      ( ~ v3_pre_topc(X0_49,sK5)
% 1.42/1.02      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(X0_49,X1_49)
% 1.42/1.02      | r1_tarski(X0_49,k1_tops_1(sK5,X1_49)) ),
% 1.42/1.02      inference(subtyping,[status(esa)],[c_616]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4286,plain,
% 1.42/1.02      ( ~ v3_pre_topc(sK8,sK5)
% 1.42/1.02      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(sK8,X0_49)
% 1.42/1.02      | r1_tarski(sK8,k1_tops_1(sK5,X0_49)) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_3818]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4288,plain,
% 1.42/1.02      ( ~ v3_pre_topc(sK8,sK5)
% 1.42/1.02      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | r1_tarski(sK8,k1_tops_1(sK5,sK7))
% 1.42/1.02      | ~ r1_tarski(sK8,sK7) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_4286]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_0,plain,
% 1.42/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 1.42/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3835,plain,
% 1.42/1.02      ( ~ r1_tarski(X0_49,X1_49)
% 1.42/1.02      | ~ r1_tarski(X2_49,X0_49)
% 1.42/1.02      | r1_tarski(X2_49,X1_49) ),
% 1.42/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4091,plain,
% 1.42/1.02      ( r1_tarski(X0_49,u1_struct_0(sK5))
% 1.42/1.02      | ~ r1_tarski(X0_49,sK7)
% 1.42/1.02      | ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_3835]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4208,plain,
% 1.42/1.02      ( r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5))
% 1.42/1.02      | ~ r1_tarski(k1_tops_1(sK5,sK7),sK7)
% 1.42/1.02      | ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_4091]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_1,plain,
% 1.42/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.42/1.02      inference(cnf_transformation,[],[f48]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3834,plain,
% 1.42/1.02      ( m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 1.42/1.02      | ~ r1_tarski(X0_49,X1_49) ),
% 1.42/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4147,plain,
% 1.42/1.02      ( m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(X0_49,u1_struct_0(sK5)) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_3834]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4184,plain,
% 1.42/1.02      ( m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5)) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_4147]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_2,plain,
% 1.42/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.42/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3833,plain,
% 1.42/1.02      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 1.42/1.02      | r1_tarski(X0_49,X1_49) ),
% 1.42/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4013,plain,
% 1.42/1.02      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | r1_tarski(sK7,u1_struct_0(sK5)) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_3833]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_7,plain,
% 1.42/1.02      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ v3_pre_topc(X1,X0) ),
% 1.42/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_18,plain,
% 1.42/1.02      ( sP1(X0,X1)
% 1.42/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.42/1.02      | ~ v2_pre_topc(X0)
% 1.42/1.02      | ~ l1_pre_topc(X0) ),
% 1.42/1.02      inference(cnf_transformation,[],[f64]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_30,negated_conjecture,
% 1.42/1.02      ( v2_pre_topc(sK5) ),
% 1.42/1.02      inference(cnf_transformation,[],[f69]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_540,plain,
% 1.42/1.02      ( sP1(sK5,X0)
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ l1_pre_topc(sK5) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_18,c_30]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_544,plain,
% 1.42/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | sP1(sK5,X0) ),
% 1.42/1.02      inference(global_propositional_subsumption,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_540,c_29]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_545,plain,
% 1.42/1.02      ( sP1(sK5,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(renaming,[status(thm)],[c_544]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_580,plain,
% 1.42/1.02      ( sP0(X0,sK5)
% 1.42/1.02      | ~ v3_pre_topc(X0,sK5)
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_7,c_545]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3820,plain,
% 1.42/1.02      ( sP0(X0_49,sK5)
% 1.42/1.02      | ~ v3_pre_topc(X0_49,sK5)
% 1.42/1.02      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(subtyping,[status(esa)],[c_580]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4008,plain,
% 1.42/1.02      ( sP0(k1_tops_1(sK5,X0_49),sK5)
% 1.42/1.02      | ~ v3_pre_topc(k1_tops_1(sK5,X0_49),sK5)
% 1.42/1.02      | ~ m1_subset_1(k1_tops_1(sK5,X0_49),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_3820]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4010,plain,
% 1.42/1.02      ( sP0(k1_tops_1(sK5,sK7),sK5)
% 1.42/1.02      | ~ v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
% 1.42/1.02      | ~ m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_4008]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_22,negated_conjecture,
% 1.42/1.02      ( ~ m1_connsp_2(sK7,sK5,sK6)
% 1.42/1.02      | ~ r2_hidden(sK6,X0)
% 1.42/1.02      | ~ v3_pre_topc(X0,sK5)
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(X0,sK7) ),
% 1.42/1.02      inference(cnf_transformation,[],[f77]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_19,plain,
% 1.42/1.02      ( m1_connsp_2(X0,X1,X2)
% 1.42/1.02      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.42/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.42/1.02      | v2_struct_0(X1)
% 1.42/1.02      | ~ v2_pre_topc(X1)
% 1.42/1.02      | ~ l1_pre_topc(X1) ),
% 1.42/1.02      inference(cnf_transformation,[],[f66]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_31,negated_conjecture,
% 1.42/1.02      ( ~ v2_struct_0(sK5) ),
% 1.42/1.02      inference(cnf_transformation,[],[f68]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_504,plain,
% 1.42/1.02      ( m1_connsp_2(X0,sK5,X1)
% 1.42/1.02      | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 1.42/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ v2_pre_topc(sK5)
% 1.42/1.02      | ~ l1_pre_topc(sK5) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_19,c_31]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_508,plain,
% 1.42/1.02      ( m1_connsp_2(X0,sK5,X1)
% 1.42/1.02      | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 1.42/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(global_propositional_subsumption,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_504,c_30,c_29]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_794,plain,
% 1.42/1.02      ( ~ r2_hidden(sK6,X0)
% 1.42/1.02      | ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 1.42/1.02      | ~ v3_pre_topc(X0,sK5)
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.42/1.02      | ~ r1_tarski(X0,sK7) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_22,c_508]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_28,negated_conjecture,
% 1.42/1.02      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.42/1.02      inference(cnf_transformation,[],[f71]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_27,negated_conjecture,
% 1.42/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(cnf_transformation,[],[f72]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_798,plain,
% 1.42/1.02      ( ~ r2_hidden(sK6,X0)
% 1.42/1.02      | ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 1.42/1.02      | ~ v3_pre_topc(X0,sK5)
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(X0,sK7) ),
% 1.42/1.02      inference(global_propositional_subsumption,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_794,c_28,c_27]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3808,plain,
% 1.42/1.02      ( ~ r2_hidden(sK6,X0_49)
% 1.42/1.02      | ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 1.42/1.02      | ~ v3_pre_topc(X0_49,sK5)
% 1.42/1.02      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(X0_49,sK7) ),
% 1.42/1.02      inference(subtyping,[status(esa)],[c_798]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3990,plain,
% 1.42/1.02      ( ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 1.42/1.02      | ~ v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
% 1.42/1.02      | ~ m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ r1_tarski(k1_tops_1(sK5,sK7),sK7) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_3808]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_4,plain,
% 1.42/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.42/1.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.42/1.02      | ~ l1_pre_topc(X1) ),
% 1.42/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_636,plain,
% 1.42/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | r1_tarski(k1_tops_1(sK5,X0),X0) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_4,c_29]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3817,plain,
% 1.42/1.02      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | r1_tarski(k1_tops_1(sK5,X0_49),X0_49) ),
% 1.42/1.02      inference(subtyping,[status(esa)],[c_636]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3885,plain,
% 1.42/1.02      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | r1_tarski(k1_tops_1(sK5,sK7),sK7) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_3817]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3,plain,
% 1.42/1.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 1.42/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.42/1.02      | ~ v2_pre_topc(X0)
% 1.42/1.02      | ~ l1_pre_topc(X0) ),
% 1.42/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_557,plain,
% 1.42/1.02      ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ l1_pre_topc(sK5) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_3,c_30]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_561,plain,
% 1.42/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | v3_pre_topc(k1_tops_1(sK5,X0),sK5) ),
% 1.42/1.02      inference(global_propositional_subsumption,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_557,c_29]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_562,plain,
% 1.42/1.02      ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(renaming,[status(thm)],[c_561]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3821,plain,
% 1.42/1.02      ( v3_pre_topc(k1_tops_1(sK5,X0_49),sK5)
% 1.42/1.02      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(subtyping,[status(esa)],[c_562]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_3873,plain,
% 1.42/1.02      ( v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
% 1.42/1.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(instantiation,[status(thm)],[c_3821]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_23,negated_conjecture,
% 1.42/1.02      ( m1_connsp_2(sK7,sK5,sK6) | r2_hidden(sK6,sK8) ),
% 1.42/1.02      inference(cnf_transformation,[],[f76]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_20,plain,
% 1.42/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 1.42/1.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.42/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.42/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.42/1.02      | v2_struct_0(X1)
% 1.42/1.02      | ~ v2_pre_topc(X1)
% 1.42/1.02      | ~ l1_pre_topc(X1) ),
% 1.42/1.02      inference(cnf_transformation,[],[f65]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_21,plain,
% 1.42/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 1.42/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.42/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.42/1.02      | v2_struct_0(X1)
% 1.42/1.02      | ~ v2_pre_topc(X1)
% 1.42/1.02      | ~ l1_pre_topc(X1) ),
% 1.42/1.02      inference(cnf_transformation,[],[f67]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_182,plain,
% 1.42/1.02      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.42/1.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.42/1.02      | ~ m1_connsp_2(X0,X1,X2)
% 1.42/1.02      | v2_struct_0(X1)
% 1.42/1.02      | ~ v2_pre_topc(X1)
% 1.42/1.02      | ~ l1_pre_topc(X1) ),
% 1.42/1.02      inference(global_propositional_subsumption,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_20,c_21]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_183,plain,
% 1.42/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 1.42/1.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.42/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.42/1.02      | v2_struct_0(X1)
% 1.42/1.02      | ~ v2_pre_topc(X1)
% 1.42/1.02      | ~ l1_pre_topc(X1) ),
% 1.42/1.02      inference(renaming,[status(thm)],[c_182]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_464,plain,
% 1.42/1.02      ( ~ m1_connsp_2(X0,sK5,X1)
% 1.42/1.02      | r2_hidden(X1,k1_tops_1(sK5,X0))
% 1.42/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.42/1.02      | ~ v2_pre_topc(sK5)
% 1.42/1.02      | ~ l1_pre_topc(sK5) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_183,c_31]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_468,plain,
% 1.42/1.02      ( ~ m1_connsp_2(X0,sK5,X1)
% 1.42/1.02      | r2_hidden(X1,k1_tops_1(sK5,X0))
% 1.42/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 1.42/1.02      inference(global_propositional_subsumption,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_464,c_30,c_29]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_781,plain,
% 1.42/1.02      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 1.42/1.02      | r2_hidden(sK6,sK8)
% 1.42/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_23,c_468]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_783,plain,
% 1.42/1.02      ( r2_hidden(sK6,sK8) | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
% 1.42/1.02      inference(global_propositional_subsumption,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_781,c_28]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_784,plain,
% 1.42/1.02      ( r2_hidden(sK6,k1_tops_1(sK5,sK7)) | r2_hidden(sK6,sK8) ),
% 1.42/1.02      inference(renaming,[status(thm)],[c_783]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_24,negated_conjecture,
% 1.42/1.02      ( m1_connsp_2(sK7,sK5,sK6) | r1_tarski(sK8,sK7) ),
% 1.42/1.02      inference(cnf_transformation,[],[f75]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_767,plain,
% 1.42/1.02      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 1.42/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.42/1.02      | r1_tarski(sK8,sK7) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_24,c_468]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_769,plain,
% 1.42/1.02      ( r2_hidden(sK6,k1_tops_1(sK5,sK7)) | r1_tarski(sK8,sK7) ),
% 1.42/1.02      inference(global_propositional_subsumption,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_767,c_28]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_25,negated_conjecture,
% 1.42/1.02      ( m1_connsp_2(sK7,sK5,sK6) | v3_pre_topc(sK8,sK5) ),
% 1.42/1.02      inference(cnf_transformation,[],[f74]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_753,plain,
% 1.42/1.02      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 1.42/1.02      | v3_pre_topc(sK8,sK5)
% 1.42/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_25,c_468]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_755,plain,
% 1.42/1.02      ( v3_pre_topc(sK8,sK5) | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
% 1.42/1.02      inference(global_propositional_subsumption,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_753,c_28]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_756,plain,
% 1.42/1.02      ( r2_hidden(sK6,k1_tops_1(sK5,sK7)) | v3_pre_topc(sK8,sK5) ),
% 1.42/1.02      inference(renaming,[status(thm)],[c_755]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_26,negated_conjecture,
% 1.42/1.02      ( m1_connsp_2(sK7,sK5,sK6)
% 1.42/1.02      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(cnf_transformation,[],[f73]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_739,plain,
% 1.42/1.02      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 1.42/1.02      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.42/1.02      inference(resolution,[status(thm)],[c_26,c_468]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_741,plain,
% 1.42/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.42/1.02      | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
% 1.42/1.02      inference(global_propositional_subsumption,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_739,c_28]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(c_742,plain,
% 1.42/1.02      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 1.42/1.02      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.42/1.02      inference(renaming,[status(thm)],[c_741]) ).
% 1.42/1.02  
% 1.42/1.02  cnf(contradiction,plain,
% 1.42/1.02      ( $false ),
% 1.42/1.02      inference(minisat,
% 1.42/1.02                [status(thm)],
% 1.42/1.02                [c_4620,c_4288,c_4208,c_4184,c_4013,c_4010,c_3990,c_3885,
% 1.42/1.02                 c_3873,c_784,c_769,c_756,c_742,c_27]) ).
% 1.42/1.02  
% 1.42/1.02  
% 1.42/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.42/1.02  
% 1.42/1.02  ------                               Statistics
% 1.42/1.02  
% 1.42/1.02  ------ General
% 1.42/1.02  
% 1.42/1.02  abstr_ref_over_cycles:                  0
% 1.42/1.02  abstr_ref_under_cycles:                 0
% 1.42/1.02  gc_basic_clause_elim:                   0
% 1.42/1.02  forced_gc_time:                         0
% 1.42/1.02  parsing_time:                           0.022
% 1.42/1.02  unif_index_cands_time:                  0.
% 1.42/1.02  unif_index_add_time:                    0.
% 1.42/1.02  orderings_time:                         0.
% 1.42/1.02  out_proof_time:                         0.014
% 1.42/1.02  total_time:                             0.136
% 1.42/1.02  num_of_symbols:                         52
% 1.42/1.02  num_of_terms:                           1904
% 1.42/1.02  
% 1.42/1.02  ------ Preprocessing
% 1.42/1.02  
% 1.42/1.02  num_of_splits:                          0
% 1.42/1.02  num_of_split_atoms:                     0
% 1.42/1.02  num_of_reused_defs:                     0
% 1.42/1.02  num_eq_ax_congr_red:                    0
% 1.42/1.02  num_of_sem_filtered_clauses:            1
% 1.42/1.02  num_of_subtypes:                        4
% 1.42/1.02  monotx_restored_types:                  0
% 1.42/1.02  sat_num_of_epr_types:                   0
% 1.42/1.02  sat_num_of_non_cyclic_types:            0
% 1.42/1.02  sat_guarded_non_collapsed_types:        0
% 1.42/1.02  num_pure_diseq_elim:                    0
% 1.42/1.02  simp_replaced_by:                       0
% 1.42/1.02  res_preprocessed:                       89
% 1.42/1.02  prep_upred:                             0
% 1.42/1.02  prep_unflattend:                        0
% 1.42/1.02  smt_new_axioms:                         0
% 1.42/1.02  pred_elim_cands:                        5
% 1.42/1.02  pred_elim:                              5
% 1.42/1.02  pred_elim_cl:                           3
% 1.42/1.02  pred_elim_cycles:                       9
% 1.42/1.02  merged_defs:                            6
% 1.42/1.02  merged_defs_ncl:                        0
% 1.42/1.02  bin_hyper_res:                          6
% 1.42/1.02  prep_cycles:                            3
% 1.42/1.02  pred_elim_time:                         0.054
% 1.42/1.02  splitting_time:                         0.
% 1.42/1.02  sem_filter_time:                        0.
% 1.42/1.02  monotx_time:                            0.
% 1.42/1.02  subtype_inf_time:                       0.
% 1.42/1.02  
% 1.42/1.02  ------ Problem properties
% 1.42/1.02  
% 1.42/1.02  clauses:                                28
% 1.42/1.02  conjectures:                            1
% 1.42/1.02  epr:                                    1
% 1.42/1.02  horn:                                   20
% 1.42/1.02  ground:                                 5
% 1.42/1.02  unary:                                  1
% 1.42/1.02  binary:                                 8
% 1.42/1.02  lits:                                   92
% 1.42/1.02  lits_eq:                                0
% 1.42/1.02  fd_pure:                                0
% 1.42/1.02  fd_pseudo:                              0
% 1.42/1.02  fd_cond:                                0
% 1.42/1.02  fd_pseudo_cond:                         0
% 1.42/1.02  ac_symbols:                             0
% 1.42/1.02  
% 1.42/1.02  ------ Propositional Solver
% 1.42/1.02  
% 1.42/1.02  prop_solver_calls:                      22
% 1.42/1.02  prop_fast_solver_calls:                 1222
% 1.42/1.02  smt_solver_calls:                       0
% 1.42/1.02  smt_fast_solver_calls:                  0
% 1.42/1.02  prop_num_of_clauses:                    809
% 1.42/1.02  prop_preprocess_simplified:             3834
% 1.42/1.02  prop_fo_subsumed:                       15
% 1.42/1.02  prop_solver_time:                       0.
% 1.42/1.02  smt_solver_time:                        0.
% 1.42/1.02  smt_fast_solver_time:                   0.
% 1.42/1.02  prop_fast_solver_time:                  0.
% 1.42/1.02  prop_unsat_core_time:                   0.
% 1.42/1.02  
% 1.42/1.02  ------ QBF
% 1.42/1.02  
% 1.42/1.02  qbf_q_res:                              0
% 1.42/1.02  qbf_num_tautologies:                    0
% 1.42/1.02  qbf_prep_cycles:                        0
% 1.42/1.02  
% 1.42/1.02  ------ BMC1
% 1.42/1.02  
% 1.42/1.02  bmc1_current_bound:                     -1
% 1.42/1.02  bmc1_last_solved_bound:                 -1
% 1.42/1.02  bmc1_unsat_core_size:                   -1
% 1.42/1.02  bmc1_unsat_core_parents_size:           -1
% 1.42/1.02  bmc1_merge_next_fun:                    0
% 1.42/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.42/1.02  
% 1.42/1.02  ------ Instantiation
% 1.42/1.02  
% 1.42/1.02  inst_num_of_clauses:                    150
% 1.42/1.02  inst_num_in_passive:                    29
% 1.42/1.02  inst_num_in_active:                     92
% 1.42/1.02  inst_num_in_unprocessed:                28
% 1.42/1.02  inst_num_of_loops:                      120
% 1.42/1.02  inst_num_of_learning_restarts:          0
% 1.42/1.02  inst_num_moves_active_passive:          22
% 1.42/1.02  inst_lit_activity:                      0
% 1.42/1.02  inst_lit_activity_moves:                0
% 1.42/1.02  inst_num_tautologies:                   0
% 1.42/1.02  inst_num_prop_implied:                  0
% 1.42/1.02  inst_num_existing_simplified:           0
% 1.42/1.02  inst_num_eq_res_simplified:             0
% 1.42/1.02  inst_num_child_elim:                    0
% 1.42/1.02  inst_num_of_dismatching_blockings:      10
% 1.42/1.02  inst_num_of_non_proper_insts:           98
% 1.42/1.02  inst_num_of_duplicates:                 0
% 1.42/1.02  inst_inst_num_from_inst_to_res:         0
% 1.42/1.02  inst_dismatching_checking_time:         0.
% 1.42/1.02  
% 1.42/1.02  ------ Resolution
% 1.42/1.02  
% 1.42/1.02  res_num_of_clauses:                     0
% 1.42/1.02  res_num_in_passive:                     0
% 1.42/1.02  res_num_in_active:                      0
% 1.42/1.02  res_num_of_loops:                       92
% 1.42/1.02  res_forward_subset_subsumed:            8
% 1.42/1.02  res_backward_subset_subsumed:           0
% 1.42/1.02  res_forward_subsumed:                   0
% 1.42/1.02  res_backward_subsumed:                  0
% 1.42/1.02  res_forward_subsumption_resolution:     0
% 1.42/1.02  res_backward_subsumption_resolution:    0
% 1.42/1.02  res_clause_to_clause_subsumption:       250
% 1.42/1.02  res_orphan_elimination:                 0
% 1.42/1.02  res_tautology_del:                      28
% 1.42/1.02  res_num_eq_res_simplified:              0
% 1.42/1.02  res_num_sel_changes:                    0
% 1.42/1.02  res_moves_from_active_to_pass:          0
% 1.42/1.02  
% 1.42/1.02  ------ Superposition
% 1.42/1.02  
% 1.42/1.02  sup_time_total:                         0.
% 1.42/1.02  sup_time_generating:                    0.
% 1.42/1.02  sup_time_sim_full:                      0.
% 1.42/1.02  sup_time_sim_immed:                     0.
% 1.42/1.02  
% 1.42/1.02  sup_num_of_clauses:                     0
% 1.42/1.02  sup_num_in_active:                      0
% 1.42/1.02  sup_num_in_passive:                     0
% 1.42/1.02  sup_num_of_loops:                       0
% 1.42/1.02  sup_fw_superposition:                   0
% 1.42/1.02  sup_bw_superposition:                   0
% 1.42/1.02  sup_immediate_simplified:               0
% 1.42/1.02  sup_given_eliminated:                   0
% 1.42/1.02  comparisons_done:                       0
% 1.42/1.02  comparisons_avoided:                    0
% 1.42/1.02  
% 1.42/1.02  ------ Simplifications
% 1.42/1.02  
% 1.42/1.02  
% 1.42/1.02  sim_fw_subset_subsumed:                 0
% 1.42/1.02  sim_bw_subset_subsumed:                 0
% 1.42/1.02  sim_fw_subsumed:                        0
% 1.42/1.02  sim_bw_subsumed:                        0
% 1.42/1.02  sim_fw_subsumption_res:                 0
% 1.42/1.02  sim_bw_subsumption_res:                 0
% 1.42/1.02  sim_tautology_del:                      0
% 1.42/1.02  sim_eq_tautology_del:                   0
% 1.42/1.02  sim_eq_res_simp:                        0
% 1.42/1.02  sim_fw_demodulated:                     0
% 1.42/1.02  sim_bw_demodulated:                     0
% 1.42/1.02  sim_light_normalised:                   0
% 1.42/1.02  sim_joinable_taut:                      0
% 1.42/1.02  sim_joinable_simp:                      0
% 1.42/1.02  sim_ac_normalised:                      0
% 1.42/1.02  sim_smt_subsumption:                    0
% 1.42/1.02  
%------------------------------------------------------------------------------
