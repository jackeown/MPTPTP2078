%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:23 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 850 expanded)
%              Number of clauses        :  106 ( 175 expanded)
%              Number of leaves         :   21 ( 251 expanded)
%              Depth                    :   20
%              Number of atoms          :  938 (9419 expanded)
%              Number of equality atoms :   63 (  89 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
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

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X0)
      | ~ r2_hidden(X5,X6)
      | ~ r1_tarski(X6,X0)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f43,f47,f46,f45,f44])).

fof(f75,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v3_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v3_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f30,f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK6,X3)
      | ~ r1_tarski(X3,sK7)
      | ~ v3_pre_topc(X3,sK5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ m1_connsp_2(sK7,sK5,sK6) ) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f40,plain,(
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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,
    ( r2_hidden(sK6,sK8)
    | m1_connsp_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,
    ( r1_tarski(sK8,sK7)
    | m1_connsp_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,
    ( v3_pre_topc(sK8,sK5)
    | m1_connsp_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_connsp_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ sP0(X2,X3)
    | ~ v3_pre_topc(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9409,plain,
    ( r2_hidden(sK6,X0)
    | ~ r2_hidden(sK6,k1_tops_1(sK5,sK8))
    | ~ sP0(X0,X1)
    | ~ v3_pre_topc(k1_tops_1(sK5,sK8),X1)
    | ~ m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(sK5,sK8),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_15155,plain,
    ( ~ r2_hidden(sK6,k1_tops_1(sK5,sK8))
    | r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ sP0(k1_tops_1(sK5,sK7),X0)
    | ~ v3_pre_topc(k1_tops_1(sK5,sK8),X0)
    | ~ m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(k1_tops_1(sK5,sK8),k1_tops_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_9409])).

cnf(c_15157,plain,
    ( ~ r2_hidden(sK6,k1_tops_1(sK5,sK8))
    | r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ sP0(k1_tops_1(sK5,sK7),sK5)
    | ~ v3_pre_topc(k1_tops_1(sK5,sK8),sK5)
    | ~ m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(k1_tops_1(sK5,sK8),k1_tops_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_15155])).

cnf(c_3045,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4855,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6,sK8)
    | X1 != sK8
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_3045])).

cnf(c_6000,plain,
    ( r2_hidden(X0,k1_tops_1(sK5,sK8))
    | ~ r2_hidden(sK6,sK8)
    | X0 != sK6
    | k1_tops_1(sK5,sK8) != sK8 ),
    inference(instantiation,[status(thm)],[c_4855])).

cnf(c_7363,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK8))
    | ~ r2_hidden(sK6,sK8)
    | k1_tops_1(sK5,sK8) != sK8
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_6000])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6859,plain,
    ( m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(k1_tops_1(sK5,sK8),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4718,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK5,sK7))
    | r1_tarski(X0,u1_struct_0(sK5))
    | ~ r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5783,plain,
    ( ~ r1_tarski(k1_tops_1(sK5,sK8),k1_tops_1(sK5,sK7))
    | r1_tarski(k1_tops_1(sK5,sK8),u1_struct_0(sK5))
    | ~ r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4718])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_31])).

cnf(c_745,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK5,X0),k1_tops_1(sK5,X1)) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_4784,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,sK8),k1_tops_1(sK5,X0))
    | ~ r1_tarski(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_5013,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,sK8),k1_tops_1(sK5,sK7))
    | ~ r1_tarski(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_4784])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_645,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_32])).

cnf(c_646,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK5)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_650,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_31])).

cnf(c_651,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_726,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(X1,X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_651,c_31])).

cnf(c_727,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_3033,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_727])).

cnf(c_6,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_620,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_32])).

cnf(c_621,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK5)
    | k1_tops_1(sK5,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_625,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK5)
    | k1_tops_1(sK5,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_621,c_31])).

cnf(c_626,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK5,X0) != X0 ),
    inference(renaming,[status(thm)],[c_625])).

cnf(c_774,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) != X0
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_626,c_31])).

cnf(c_775,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_774])).

cnf(c_3030,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_775])).

cnf(c_3034,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_727])).

cnf(c_3158,plain,
    ( k1_tops_1(sK5,X0) = X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3033,c_3030,c_3034])).

cnf(c_3159,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) = X0 ),
    inference(renaming,[status(thm)],[c_3158])).

cnf(c_4834,plain,
    ( ~ v3_pre_topc(sK8,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,sK8) = sK8 ),
    inference(instantiation,[status(thm)],[c_3159])).

cnf(c_3,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_602,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_32])).

cnf(c_603,plain,
    ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_607,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(k1_tops_1(sK5,X0),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_31])).

cnf(c_608,plain,
    ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_607])).

cnf(c_4787,plain,
    ( v3_pre_topc(k1_tops_1(sK5,sK8),sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_4719,plain,
    ( m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4203,plain,
    ( r1_tarski(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X0,sK7)
    | ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4413,plain,
    ( r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5))
    | ~ r1_tarski(k1_tops_1(sK5,sK7),sK7)
    | ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4203])).

cnf(c_9,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v3_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_584,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_585,plain,
    ( sP1(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | sP1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_31])).

cnf(c_590,plain,
    ( sP1(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_589])).

cnf(c_688,plain,
    ( sP0(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | X2 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_590])).

cnf(c_689,plain,
    ( sP0(X0,sK5)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_4286,plain,
    ( sP0(k1_tops_1(sK5,sK7),sK5)
    | ~ v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
    | ~ m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_3036,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4237,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3036])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4107,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_24,negated_conjecture,
    ( ~ m1_connsp_2(sK7,sK5,sK6)
    | ~ r2_hidden(sK6,X0)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_547,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_548,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_552,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_32,c_31])).

cnf(c_956,plain,
    ( ~ r2_hidden(X0,k1_tops_1(sK5,X1))
    | ~ r2_hidden(sK6,X2)
    | ~ v3_pre_topc(X2,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X2,sK7)
    | sK5 != sK5
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_552])).

cnf(c_957,plain,
    ( ~ r2_hidden(sK6,X0)
    | ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r1_tarski(X0,sK7) ),
    inference(unflattening,[status(thm)],[c_956])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_961,plain,
    ( ~ r2_hidden(sK6,X0)
    | ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_957,c_30,c_29])).

cnf(c_4093,plain,
    ( ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
    | ~ m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(k1_tops_1(sK5,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_762,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_31])).

cnf(c_763,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,X0),X0) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_4074,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_4071,plain,
    ( v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_25,negated_conjecture,
    ( m1_connsp_2(sK7,sK5,sK6)
    | r2_hidden(sK6,sK8) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_22,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_23])).

cnf(c_195,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_194])).

cnf(c_505,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_33])).

cnf(c_506,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_510,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_32,c_31])).

cnf(c_942,plain,
    ( r2_hidden(X0,k1_tops_1(sK5,X1))
    | r2_hidden(sK6,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | sK5 != sK5
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_510])).

cnf(c_943,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | r2_hidden(sK6,sK8)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_942])).

cnf(c_945,plain,
    ( r2_hidden(sK6,sK8)
    | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_943,c_30])).

cnf(c_946,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | r2_hidden(sK6,sK8) ),
    inference(renaming,[status(thm)],[c_945])).

cnf(c_26,negated_conjecture,
    ( m1_connsp_2(sK7,sK5,sK6)
    | r1_tarski(sK8,sK7) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_926,plain,
    ( r2_hidden(X0,k1_tops_1(sK5,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_tarski(sK8,sK7)
    | sK5 != sK5
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_510])).

cnf(c_927,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | r1_tarski(sK8,sK7) ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_929,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | r1_tarski(sK8,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_927,c_30])).

cnf(c_27,negated_conjecture,
    ( m1_connsp_2(sK7,sK5,sK6)
    | v3_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_910,plain,
    ( r2_hidden(X0,k1_tops_1(sK5,X1))
    | v3_pre_topc(sK8,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | sK5 != sK5
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_510])).

cnf(c_911,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | v3_pre_topc(sK8,sK5)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_913,plain,
    ( v3_pre_topc(sK8,sK5)
    | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_911,c_30])).

cnf(c_914,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | v3_pre_topc(sK8,sK5) ),
    inference(renaming,[status(thm)],[c_913])).

cnf(c_28,negated_conjecture,
    ( m1_connsp_2(sK7,sK5,sK6)
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_894,plain,
    ( r2_hidden(X0,k1_tops_1(sK5,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | sK5 != sK5
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_510])).

cnf(c_895,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_897,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_895,c_30])).

cnf(c_898,plain,
    ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_897])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15157,c_7363,c_6859,c_5783,c_5013,c_4834,c_4787,c_4719,c_4413,c_4286,c_4237,c_4107,c_4093,c_4074,c_4071,c_946,c_929,c_914,c_898,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:21:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.70/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/0.99  
% 2.70/0.99  ------  iProver source info
% 2.70/0.99  
% 2.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/0.99  git: non_committed_changes: false
% 2.70/0.99  git: last_make_outside_of_git: false
% 2.70/0.99  
% 2.70/0.99  ------ 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options
% 2.70/0.99  
% 2.70/0.99  --out_options                           all
% 2.70/0.99  --tptp_safe_out                         true
% 2.70/0.99  --problem_path                          ""
% 2.70/0.99  --include_path                          ""
% 2.70/0.99  --clausifier                            res/vclausify_rel
% 2.70/0.99  --clausifier_options                    --mode clausify
% 2.70/0.99  --stdin                                 false
% 2.70/0.99  --stats_out                             all
% 2.70/0.99  
% 2.70/0.99  ------ General Options
% 2.70/0.99  
% 2.70/0.99  --fof                                   false
% 2.70/0.99  --time_out_real                         305.
% 2.70/0.99  --time_out_virtual                      -1.
% 2.70/0.99  --symbol_type_check                     false
% 2.70/0.99  --clausify_out                          false
% 2.70/0.99  --sig_cnt_out                           false
% 2.70/0.99  --trig_cnt_out                          false
% 2.70/0.99  --trig_cnt_out_tolerance                1.
% 2.70/0.99  --trig_cnt_out_sk_spl                   false
% 2.70/0.99  --abstr_cl_out                          false
% 2.70/0.99  
% 2.70/0.99  ------ Global Options
% 2.70/0.99  
% 2.70/0.99  --schedule                              default
% 2.70/0.99  --add_important_lit                     false
% 2.70/0.99  --prop_solver_per_cl                    1000
% 2.70/0.99  --min_unsat_core                        false
% 2.70/0.99  --soft_assumptions                      false
% 2.70/0.99  --soft_lemma_size                       3
% 2.70/0.99  --prop_impl_unit_size                   0
% 2.70/0.99  --prop_impl_unit                        []
% 2.70/0.99  --share_sel_clauses                     true
% 2.70/0.99  --reset_solvers                         false
% 2.70/0.99  --bc_imp_inh                            [conj_cone]
% 2.70/0.99  --conj_cone_tolerance                   3.
% 2.70/0.99  --extra_neg_conj                        none
% 2.70/0.99  --large_theory_mode                     true
% 2.70/0.99  --prolific_symb_bound                   200
% 2.70/0.99  --lt_threshold                          2000
% 2.70/0.99  --clause_weak_htbl                      true
% 2.70/0.99  --gc_record_bc_elim                     false
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing Options
% 2.70/0.99  
% 2.70/0.99  --preprocessing_flag                    true
% 2.70/0.99  --time_out_prep_mult                    0.1
% 2.70/0.99  --splitting_mode                        input
% 2.70/0.99  --splitting_grd                         true
% 2.70/0.99  --splitting_cvd                         false
% 2.70/0.99  --splitting_cvd_svl                     false
% 2.70/0.99  --splitting_nvd                         32
% 2.70/0.99  --sub_typing                            true
% 2.70/0.99  --prep_gs_sim                           true
% 2.70/0.99  --prep_unflatten                        true
% 2.70/0.99  --prep_res_sim                          true
% 2.70/0.99  --prep_upred                            true
% 2.70/0.99  --prep_sem_filter                       exhaustive
% 2.70/0.99  --prep_sem_filter_out                   false
% 2.70/0.99  --pred_elim                             true
% 2.70/0.99  --res_sim_input                         true
% 2.70/0.99  --eq_ax_congr_red                       true
% 2.70/0.99  --pure_diseq_elim                       true
% 2.70/0.99  --brand_transform                       false
% 2.70/0.99  --non_eq_to_eq                          false
% 2.70/0.99  --prep_def_merge                        true
% 2.70/0.99  --prep_def_merge_prop_impl              false
% 2.70/0.99  --prep_def_merge_mbd                    true
% 2.70/0.99  --prep_def_merge_tr_red                 false
% 2.70/0.99  --prep_def_merge_tr_cl                  false
% 2.70/0.99  --smt_preprocessing                     true
% 2.70/0.99  --smt_ac_axioms                         fast
% 2.70/0.99  --preprocessed_out                      false
% 2.70/0.99  --preprocessed_stats                    false
% 2.70/0.99  
% 2.70/0.99  ------ Abstraction refinement Options
% 2.70/0.99  
% 2.70/0.99  --abstr_ref                             []
% 2.70/0.99  --abstr_ref_prep                        false
% 2.70/0.99  --abstr_ref_until_sat                   false
% 2.70/0.99  --abstr_ref_sig_restrict                funpre
% 2.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.99  --abstr_ref_under                       []
% 2.70/0.99  
% 2.70/0.99  ------ SAT Options
% 2.70/0.99  
% 2.70/0.99  --sat_mode                              false
% 2.70/0.99  --sat_fm_restart_options                ""
% 2.70/0.99  --sat_gr_def                            false
% 2.70/0.99  --sat_epr_types                         true
% 2.70/0.99  --sat_non_cyclic_types                  false
% 2.70/0.99  --sat_finite_models                     false
% 2.70/0.99  --sat_fm_lemmas                         false
% 2.70/0.99  --sat_fm_prep                           false
% 2.70/0.99  --sat_fm_uc_incr                        true
% 2.70/0.99  --sat_out_model                         small
% 2.70/0.99  --sat_out_clauses                       false
% 2.70/0.99  
% 2.70/0.99  ------ QBF Options
% 2.70/0.99  
% 2.70/0.99  --qbf_mode                              false
% 2.70/0.99  --qbf_elim_univ                         false
% 2.70/0.99  --qbf_dom_inst                          none
% 2.70/0.99  --qbf_dom_pre_inst                      false
% 2.70/0.99  --qbf_sk_in                             false
% 2.70/0.99  --qbf_pred_elim                         true
% 2.70/0.99  --qbf_split                             512
% 2.70/0.99  
% 2.70/0.99  ------ BMC1 Options
% 2.70/0.99  
% 2.70/0.99  --bmc1_incremental                      false
% 2.70/0.99  --bmc1_axioms                           reachable_all
% 2.70/0.99  --bmc1_min_bound                        0
% 2.70/0.99  --bmc1_max_bound                        -1
% 2.70/0.99  --bmc1_max_bound_default                -1
% 2.70/0.99  --bmc1_symbol_reachability              true
% 2.70/0.99  --bmc1_property_lemmas                  false
% 2.70/0.99  --bmc1_k_induction                      false
% 2.70/0.99  --bmc1_non_equiv_states                 false
% 2.70/0.99  --bmc1_deadlock                         false
% 2.70/0.99  --bmc1_ucm                              false
% 2.70/0.99  --bmc1_add_unsat_core                   none
% 2.70/0.99  --bmc1_unsat_core_children              false
% 2.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.99  --bmc1_out_stat                         full
% 2.70/0.99  --bmc1_ground_init                      false
% 2.70/0.99  --bmc1_pre_inst_next_state              false
% 2.70/0.99  --bmc1_pre_inst_state                   false
% 2.70/0.99  --bmc1_pre_inst_reach_state             false
% 2.70/0.99  --bmc1_out_unsat_core                   false
% 2.70/0.99  --bmc1_aig_witness_out                  false
% 2.70/0.99  --bmc1_verbose                          false
% 2.70/0.99  --bmc1_dump_clauses_tptp                false
% 2.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.99  --bmc1_dump_file                        -
% 2.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.99  --bmc1_ucm_extend_mode                  1
% 2.70/0.99  --bmc1_ucm_init_mode                    2
% 2.70/0.99  --bmc1_ucm_cone_mode                    none
% 2.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.99  --bmc1_ucm_relax_model                  4
% 2.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.99  --bmc1_ucm_layered_model                none
% 2.70/0.99  --bmc1_ucm_max_lemma_size               10
% 2.70/0.99  
% 2.70/0.99  ------ AIG Options
% 2.70/0.99  
% 2.70/0.99  --aig_mode                              false
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation Options
% 2.70/0.99  
% 2.70/0.99  --instantiation_flag                    true
% 2.70/0.99  --inst_sos_flag                         false
% 2.70/0.99  --inst_sos_phase                        true
% 2.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel_side                     num_symb
% 2.70/0.99  --inst_solver_per_active                1400
% 2.70/0.99  --inst_solver_calls_frac                1.
% 2.70/0.99  --inst_passive_queue_type               priority_queues
% 2.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.99  --inst_passive_queues_freq              [25;2]
% 2.70/0.99  --inst_dismatching                      true
% 2.70/0.99  --inst_eager_unprocessed_to_passive     true
% 2.70/0.99  --inst_prop_sim_given                   true
% 2.70/0.99  --inst_prop_sim_new                     false
% 2.70/0.99  --inst_subs_new                         false
% 2.70/0.99  --inst_eq_res_simp                      false
% 2.70/0.99  --inst_subs_given                       false
% 2.70/0.99  --inst_orphan_elimination               true
% 2.70/0.99  --inst_learning_loop_flag               true
% 2.70/0.99  --inst_learning_start                   3000
% 2.70/0.99  --inst_learning_factor                  2
% 2.70/0.99  --inst_start_prop_sim_after_learn       3
% 2.70/0.99  --inst_sel_renew                        solver
% 2.70/0.99  --inst_lit_activity_flag                true
% 2.70/0.99  --inst_restr_to_given                   false
% 2.70/0.99  --inst_activity_threshold               500
% 2.70/0.99  --inst_out_proof                        true
% 2.70/0.99  
% 2.70/0.99  ------ Resolution Options
% 2.70/0.99  
% 2.70/0.99  --resolution_flag                       true
% 2.70/0.99  --res_lit_sel                           adaptive
% 2.70/0.99  --res_lit_sel_side                      none
% 2.70/0.99  --res_ordering                          kbo
% 2.70/0.99  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     false
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   []
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_full_bw                           [BwDemod]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  ------ Parsing...
% 2.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/0.99  ------ Proving...
% 2.70/0.99  ------ Problem Properties 
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  clauses                                 35
% 2.70/0.99  conjectures                             2
% 2.70/0.99  EPR                                     3
% 2.70/0.99  Horn                                    25
% 2.70/0.99  unary                                   2
% 2.70/0.99  binary                                  12
% 2.70/0.99  lits                                    108
% 2.70/0.99  lits eq                                 2
% 2.70/0.99  fd_pure                                 0
% 2.70/0.99  fd_pseudo                               0
% 2.70/0.99  fd_cond                                 0
% 2.70/0.99  fd_pseudo_cond                          0
% 2.70/0.99  AC symbols                              0
% 2.70/0.99  
% 2.70/0.99  ------ Schedule dynamic 5 is on 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ 
% 2.70/0.99  Current options:
% 2.70/0.99  ------ 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options
% 2.70/0.99  
% 2.70/0.99  --out_options                           all
% 2.70/0.99  --tptp_safe_out                         true
% 2.70/0.99  --problem_path                          ""
% 2.70/0.99  --include_path                          ""
% 2.70/0.99  --clausifier                            res/vclausify_rel
% 2.70/0.99  --clausifier_options                    --mode clausify
% 2.70/0.99  --stdin                                 false
% 2.70/0.99  --stats_out                             all
% 2.70/0.99  
% 2.70/0.99  ------ General Options
% 2.70/0.99  
% 2.70/0.99  --fof                                   false
% 2.70/0.99  --time_out_real                         305.
% 2.70/0.99  --time_out_virtual                      -1.
% 2.70/0.99  --symbol_type_check                     false
% 2.70/0.99  --clausify_out                          false
% 2.70/0.99  --sig_cnt_out                           false
% 2.70/0.99  --trig_cnt_out                          false
% 2.70/0.99  --trig_cnt_out_tolerance                1.
% 2.70/0.99  --trig_cnt_out_sk_spl                   false
% 2.70/0.99  --abstr_cl_out                          false
% 2.70/0.99  
% 2.70/0.99  ------ Global Options
% 2.70/0.99  
% 2.70/0.99  --schedule                              default
% 2.70/0.99  --add_important_lit                     false
% 2.70/0.99  --prop_solver_per_cl                    1000
% 2.70/0.99  --min_unsat_core                        false
% 2.70/0.99  --soft_assumptions                      false
% 2.70/0.99  --soft_lemma_size                       3
% 2.70/0.99  --prop_impl_unit_size                   0
% 2.70/0.99  --prop_impl_unit                        []
% 2.70/0.99  --share_sel_clauses                     true
% 2.70/0.99  --reset_solvers                         false
% 2.70/0.99  --bc_imp_inh                            [conj_cone]
% 2.70/0.99  --conj_cone_tolerance                   3.
% 2.70/0.99  --extra_neg_conj                        none
% 2.70/0.99  --large_theory_mode                     true
% 2.70/0.99  --prolific_symb_bound                   200
% 2.70/0.99  --lt_threshold                          2000
% 2.70/0.99  --clause_weak_htbl                      true
% 2.70/0.99  --gc_record_bc_elim                     false
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing Options
% 2.70/0.99  
% 2.70/0.99  --preprocessing_flag                    true
% 2.70/0.99  --time_out_prep_mult                    0.1
% 2.70/0.99  --splitting_mode                        input
% 2.70/0.99  --splitting_grd                         true
% 2.70/0.99  --splitting_cvd                         false
% 2.70/0.99  --splitting_cvd_svl                     false
% 2.70/0.99  --splitting_nvd                         32
% 2.70/0.99  --sub_typing                            true
% 2.70/0.99  --prep_gs_sim                           true
% 2.70/0.99  --prep_unflatten                        true
% 2.70/0.99  --prep_res_sim                          true
% 2.70/0.99  --prep_upred                            true
% 2.70/0.99  --prep_sem_filter                       exhaustive
% 2.70/0.99  --prep_sem_filter_out                   false
% 2.70/0.99  --pred_elim                             true
% 2.70/0.99  --res_sim_input                         true
% 2.70/0.99  --eq_ax_congr_red                       true
% 2.70/0.99  --pure_diseq_elim                       true
% 2.70/0.99  --brand_transform                       false
% 2.70/0.99  --non_eq_to_eq                          false
% 2.70/0.99  --prep_def_merge                        true
% 2.70/0.99  --prep_def_merge_prop_impl              false
% 2.70/0.99  --prep_def_merge_mbd                    true
% 2.70/0.99  --prep_def_merge_tr_red                 false
% 2.70/0.99  --prep_def_merge_tr_cl                  false
% 2.70/0.99  --smt_preprocessing                     true
% 2.70/0.99  --smt_ac_axioms                         fast
% 2.70/0.99  --preprocessed_out                      false
% 2.70/0.99  --preprocessed_stats                    false
% 2.70/0.99  
% 2.70/0.99  ------ Abstraction refinement Options
% 2.70/0.99  
% 2.70/0.99  --abstr_ref                             []
% 2.70/0.99  --abstr_ref_prep                        false
% 2.70/0.99  --abstr_ref_until_sat                   false
% 2.70/0.99  --abstr_ref_sig_restrict                funpre
% 2.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.99  --abstr_ref_under                       []
% 2.70/0.99  
% 2.70/0.99  ------ SAT Options
% 2.70/0.99  
% 2.70/0.99  --sat_mode                              false
% 2.70/0.99  --sat_fm_restart_options                ""
% 2.70/0.99  --sat_gr_def                            false
% 2.70/0.99  --sat_epr_types                         true
% 2.70/0.99  --sat_non_cyclic_types                  false
% 2.70/0.99  --sat_finite_models                     false
% 2.70/0.99  --sat_fm_lemmas                         false
% 2.70/0.99  --sat_fm_prep                           false
% 2.70/0.99  --sat_fm_uc_incr                        true
% 2.70/0.99  --sat_out_model                         small
% 2.70/0.99  --sat_out_clauses                       false
% 2.70/0.99  
% 2.70/0.99  ------ QBF Options
% 2.70/0.99  
% 2.70/0.99  --qbf_mode                              false
% 2.70/0.99  --qbf_elim_univ                         false
% 2.70/0.99  --qbf_dom_inst                          none
% 2.70/0.99  --qbf_dom_pre_inst                      false
% 2.70/0.99  --qbf_sk_in                             false
% 2.70/0.99  --qbf_pred_elim                         true
% 2.70/0.99  --qbf_split                             512
% 2.70/0.99  
% 2.70/0.99  ------ BMC1 Options
% 2.70/0.99  
% 2.70/0.99  --bmc1_incremental                      false
% 2.70/0.99  --bmc1_axioms                           reachable_all
% 2.70/0.99  --bmc1_min_bound                        0
% 2.70/0.99  --bmc1_max_bound                        -1
% 2.70/0.99  --bmc1_max_bound_default                -1
% 2.70/0.99  --bmc1_symbol_reachability              true
% 2.70/0.99  --bmc1_property_lemmas                  false
% 2.70/0.99  --bmc1_k_induction                      false
% 2.70/0.99  --bmc1_non_equiv_states                 false
% 2.70/0.99  --bmc1_deadlock                         false
% 2.70/0.99  --bmc1_ucm                              false
% 2.70/0.99  --bmc1_add_unsat_core                   none
% 2.70/0.99  --bmc1_unsat_core_children              false
% 2.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.99  --bmc1_out_stat                         full
% 2.70/0.99  --bmc1_ground_init                      false
% 2.70/0.99  --bmc1_pre_inst_next_state              false
% 2.70/0.99  --bmc1_pre_inst_state                   false
% 2.70/0.99  --bmc1_pre_inst_reach_state             false
% 2.70/0.99  --bmc1_out_unsat_core                   false
% 2.70/0.99  --bmc1_aig_witness_out                  false
% 2.70/0.99  --bmc1_verbose                          false
% 2.70/0.99  --bmc1_dump_clauses_tptp                false
% 2.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.99  --bmc1_dump_file                        -
% 2.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.99  --bmc1_ucm_extend_mode                  1
% 2.70/0.99  --bmc1_ucm_init_mode                    2
% 2.70/0.99  --bmc1_ucm_cone_mode                    none
% 2.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.99  --bmc1_ucm_relax_model                  4
% 2.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.99  --bmc1_ucm_layered_model                none
% 2.70/0.99  --bmc1_ucm_max_lemma_size               10
% 2.70/0.99  
% 2.70/0.99  ------ AIG Options
% 2.70/0.99  
% 2.70/0.99  --aig_mode                              false
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation Options
% 2.70/0.99  
% 2.70/0.99  --instantiation_flag                    true
% 2.70/0.99  --inst_sos_flag                         false
% 2.70/0.99  --inst_sos_phase                        true
% 2.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel_side                     none
% 2.70/0.99  --inst_solver_per_active                1400
% 2.70/0.99  --inst_solver_calls_frac                1.
% 2.70/0.99  --inst_passive_queue_type               priority_queues
% 2.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.99  --inst_passive_queues_freq              [25;2]
% 2.70/0.99  --inst_dismatching                      true
% 2.70/0.99  --inst_eager_unprocessed_to_passive     true
% 2.70/0.99  --inst_prop_sim_given                   true
% 2.70/0.99  --inst_prop_sim_new                     false
% 2.70/0.99  --inst_subs_new                         false
% 2.70/0.99  --inst_eq_res_simp                      false
% 2.70/0.99  --inst_subs_given                       false
% 2.70/0.99  --inst_orphan_elimination               true
% 2.70/0.99  --inst_learning_loop_flag               true
% 2.70/0.99  --inst_learning_start                   3000
% 2.70/0.99  --inst_learning_factor                  2
% 2.70/0.99  --inst_start_prop_sim_after_learn       3
% 2.70/0.99  --inst_sel_renew                        solver
% 2.70/0.99  --inst_lit_activity_flag                true
% 2.70/0.99  --inst_restr_to_given                   false
% 2.70/0.99  --inst_activity_threshold               500
% 2.70/0.99  --inst_out_proof                        true
% 2.70/0.99  
% 2.70/0.99  ------ Resolution Options
% 2.70/0.99  
% 2.70/0.99  --resolution_flag                       false
% 2.70/0.99  --res_lit_sel                           adaptive
% 2.70/0.99  --res_lit_sel_side                      none
% 2.70/0.99  --res_ordering                          kbo
% 2.70/0.99  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     false
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   []
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_full_bw                           [BwDemod]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ Proving...
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS status Theorem for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  fof(f29,plain,(
% 2.70/0.99    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.70/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.70/0.99  
% 2.70/0.99  fof(f34,plain,(
% 2.70/0.99    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1))) | ~sP0(X1,X0)))),
% 2.70/0.99    inference(nnf_transformation,[],[f29])).
% 2.70/0.99  
% 2.70/0.99  fof(f35,plain,(
% 2.70/0.99    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 2.70/0.99    inference(rectify,[],[f34])).
% 2.70/0.99  
% 2.70/0.99  fof(f38,plain,(
% 2.70/0.99    ! [X5,X1,X0] : (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X5,sK4(X0,X1,X5)) & r1_tarski(sK4(X0,X1,X5),X0) & v3_pre_topc(sK4(X0,X1,X5),X1) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f37,plain,(
% 2.70/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X2,sK3(X0,X1)) & r1_tarski(sK3(X0,X1),X0) & v3_pre_topc(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f36,plain,(
% 2.70/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0))) => ((! [X3] : (~r2_hidden(sK2(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),X0)) & (? [X4] : (r2_hidden(sK2(X0,X1),X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),X0))))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f39,plain,(
% 2.70/0.99    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (~r2_hidden(sK2(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),X0)) & ((r2_hidden(sK2(X0,X1),sK3(X0,X1)) & r1_tarski(sK3(X0,X1),X0) & v3_pre_topc(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((r2_hidden(X5,sK4(X0,X1,X5)) & r1_tarski(sK4(X0,X1,X5),X0) & v3_pre_topc(sK4(X0,X1,X5),X1) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).
% 2.70/0.99  
% 2.70/0.99  fof(f63,plain,(
% 2.70/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X0) | ~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f39])).
% 2.70/0.99  
% 2.70/0.99  fof(f2,axiom,(
% 2.70/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f32,plain,(
% 2.70/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.70/0.99    inference(nnf_transformation,[],[f2])).
% 2.70/0.99  
% 2.70/0.99  fof(f51,plain,(
% 2.70/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f32])).
% 2.70/0.99  
% 2.70/0.99  fof(f1,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f12,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.70/0.99    inference(ennf_transformation,[],[f1])).
% 2.70/0.99  
% 2.70/0.99  fof(f13,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.70/0.99    inference(flattening,[],[f12])).
% 2.70/0.99  
% 2.70/0.99  fof(f49,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f13])).
% 2.70/0.99  
% 2.70/0.99  fof(f5,axiom,(
% 2.70/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f17,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f5])).
% 2.70/0.99  
% 2.70/0.99  fof(f18,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.99    inference(flattening,[],[f17])).
% 2.70/0.99  
% 2.70/0.99  fof(f54,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f18])).
% 2.70/0.99  
% 2.70/0.99  fof(f10,conjecture,(
% 2.70/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f11,negated_conjecture,(
% 2.70/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.70/0.99    inference(negated_conjecture,[],[f10])).
% 2.70/0.99  
% 2.70/0.99  fof(f27,plain,(
% 2.70/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f11])).
% 2.70/0.99  
% 2.70/0.99  fof(f28,plain,(
% 2.70/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.70/0.99    inference(flattening,[],[f27])).
% 2.70/0.99  
% 2.70/0.99  fof(f41,plain,(
% 2.70/0.99    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.70/0.99    inference(nnf_transformation,[],[f28])).
% 2.70/0.99  
% 2.70/0.99  fof(f42,plain,(
% 2.70/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.70/0.99    inference(flattening,[],[f41])).
% 2.70/0.99  
% 2.70/0.99  fof(f43,plain,(
% 2.70/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.70/0.99    inference(rectify,[],[f42])).
% 2.70/0.99  
% 2.70/0.99  fof(f47,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK8) & r1_tarski(sK8,X2) & v3_pre_topc(sK8,X0) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f46,plain,(
% 2.70/0.99    ( ! [X0,X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,sK7) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(sK7,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,sK7) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(sK7,X0,X1)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f45,plain,(
% 2.70/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK6,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,sK6)) & (? [X4] : (r2_hidden(sK6,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,sK6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f44,plain,(
% 2.70/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK5) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))) | ~m1_connsp_2(X2,sK5,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK5) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK5)))) | m1_connsp_2(X2,sK5,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f48,plain,(
% 2.70/0.99    (((! [X3] : (~r2_hidden(sK6,X3) | ~r1_tarski(X3,sK7) | ~v3_pre_topc(X3,sK5) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))) | ~m1_connsp_2(sK7,sK5,sK6)) & ((r2_hidden(sK6,sK8) & r1_tarski(sK8,sK7) & v3_pre_topc(sK8,sK5) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))) | m1_connsp_2(sK7,sK5,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f43,f47,f46,f45,f44])).
% 2.70/0.99  
% 2.70/0.99  fof(f75,plain,(
% 2.70/0.99    l1_pre_topc(sK5)),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f6,axiom,(
% 2.70/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f19,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f6])).
% 2.70/0.99  
% 2.70/0.99  fof(f20,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.70/0.99    inference(flattening,[],[f19])).
% 2.70/0.99  
% 2.70/0.99  fof(f55,plain,(
% 2.70/0.99    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f20])).
% 2.70/0.99  
% 2.70/0.99  fof(f74,plain,(
% 2.70/0.99    v2_pre_topc(sK5)),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f56,plain,(
% 2.70/0.99    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f20])).
% 2.70/0.99  
% 2.70/0.99  fof(f3,axiom,(
% 2.70/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f14,plain,(
% 2.70/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f3])).
% 2.70/0.99  
% 2.70/0.99  fof(f15,plain,(
% 2.70/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.70/0.99    inference(flattening,[],[f14])).
% 2.70/0.99  
% 2.70/0.99  fof(f52,plain,(
% 2.70/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f15])).
% 2.70/0.99  
% 2.70/0.99  fof(f30,plain,(
% 2.70/0.99    ! [X0,X1] : ((v3_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 2.70/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.70/0.99  
% 2.70/0.99  fof(f33,plain,(
% 2.70/0.99    ! [X0,X1] : (((v3_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 2.70/0.99    inference(nnf_transformation,[],[f30])).
% 2.70/0.99  
% 2.70/0.99  fof(f57,plain,(
% 2.70/0.99    ( ! [X0,X1] : (sP0(X1,X0) | ~v3_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f33])).
% 2.70/0.99  
% 2.70/0.99  fof(f7,axiom,(
% 2.70/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f21,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f7])).
% 2.70/0.99  
% 2.70/0.99  fof(f22,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.70/0.99    inference(flattening,[],[f21])).
% 2.70/0.99  
% 2.70/0.99  fof(f31,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.70/0.99    inference(definition_folding,[],[f22,f30,f29])).
% 2.70/0.99  
% 2.70/0.99  fof(f69,plain,(
% 2.70/0.99    ( ! [X0,X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f31])).
% 2.70/0.99  
% 2.70/0.99  fof(f50,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f32])).
% 2.70/0.99  
% 2.70/0.99  fof(f82,plain,(
% 2.70/0.99    ( ! [X3] : (~r2_hidden(sK6,X3) | ~r1_tarski(X3,sK7) | ~v3_pre_topc(X3,sK5) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_connsp_2(sK7,sK5,sK6)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f8,axiom,(
% 2.70/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f23,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f8])).
% 2.70/0.99  
% 2.70/0.99  fof(f24,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/0.99    inference(flattening,[],[f23])).
% 2.70/0.99  
% 2.70/0.99  fof(f40,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/0.99    inference(nnf_transformation,[],[f24])).
% 2.70/0.99  
% 2.70/0.99  fof(f71,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f40])).
% 2.70/0.99  
% 2.70/0.99  fof(f73,plain,(
% 2.70/0.99    ~v2_struct_0(sK5)),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f76,plain,(
% 2.70/0.99    m1_subset_1(sK6,u1_struct_0(sK5))),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f77,plain,(
% 2.70/0.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f4,axiom,(
% 2.70/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f16,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f4])).
% 2.70/0.99  
% 2.70/0.99  fof(f53,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f16])).
% 2.70/0.99  
% 2.70/0.99  fof(f81,plain,(
% 2.70/0.99    r2_hidden(sK6,sK8) | m1_connsp_2(sK7,sK5,sK6)),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f70,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f40])).
% 2.70/0.99  
% 2.70/0.99  fof(f9,axiom,(
% 2.70/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f25,plain,(
% 2.70/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f9])).
% 2.70/0.99  
% 2.70/0.99  fof(f26,plain,(
% 2.70/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/0.99    inference(flattening,[],[f25])).
% 2.70/0.99  
% 2.70/0.99  fof(f72,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f26])).
% 2.70/0.99  
% 2.70/0.99  fof(f80,plain,(
% 2.70/0.99    r1_tarski(sK8,sK7) | m1_connsp_2(sK7,sK5,sK6)),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f79,plain,(
% 2.70/0.99    v3_pre_topc(sK8,sK5) | m1_connsp_2(sK7,sK5,sK6)),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f78,plain,(
% 2.70/0.99    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) | m1_connsp_2(sK7,sK5,sK6)),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  cnf(c_15,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,X1)
% 2.70/0.99      | r2_hidden(X0,X2)
% 2.70/0.99      | ~ sP0(X2,X3)
% 2.70/0.99      | ~ v3_pre_topc(X1,X3)
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
% 2.70/0.99      | ~ r1_tarski(X1,X2) ),
% 2.70/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_9409,plain,
% 2.70/0.99      ( r2_hidden(sK6,X0)
% 2.70/0.99      | ~ r2_hidden(sK6,k1_tops_1(sK5,sK8))
% 2.70/0.99      | ~ sP0(X0,X1)
% 2.70/0.99      | ~ v3_pre_topc(k1_tops_1(sK5,sK8),X1)
% 2.70/0.99      | ~ m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ r1_tarski(k1_tops_1(sK5,sK8),X0) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_15155,plain,
% 2.70/0.99      ( ~ r2_hidden(sK6,k1_tops_1(sK5,sK8))
% 2.70/0.99      | r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 2.70/0.99      | ~ sP0(k1_tops_1(sK5,sK7),X0)
% 2.70/0.99      | ~ v3_pre_topc(k1_tops_1(sK5,sK8),X0)
% 2.70/0.99      | ~ m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(X0)))
% 2.70/0.99      | ~ r1_tarski(k1_tops_1(sK5,sK8),k1_tops_1(sK5,sK7)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_9409]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_15157,plain,
% 2.70/0.99      ( ~ r2_hidden(sK6,k1_tops_1(sK5,sK8))
% 2.70/0.99      | r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 2.70/0.99      | ~ sP0(k1_tops_1(sK5,sK7),sK5)
% 2.70/0.99      | ~ v3_pre_topc(k1_tops_1(sK5,sK8),sK5)
% 2.70/0.99      | ~ m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ r1_tarski(k1_tops_1(sK5,sK8),k1_tops_1(sK5,sK7)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_15155]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3045,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4855,plain,
% 2.70/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(sK6,sK8) | X1 != sK8 | X0 != sK6 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_3045]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_6000,plain,
% 2.70/0.99      ( r2_hidden(X0,k1_tops_1(sK5,sK8))
% 2.70/0.99      | ~ r2_hidden(sK6,sK8)
% 2.70/0.99      | X0 != sK6
% 2.70/0.99      | k1_tops_1(sK5,sK8) != sK8 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_4855]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_7363,plain,
% 2.70/0.99      ( r2_hidden(sK6,k1_tops_1(sK5,sK8))
% 2.70/0.99      | ~ r2_hidden(sK6,sK8)
% 2.70/0.99      | k1_tops_1(sK5,sK8) != sK8
% 2.70/0.99      | sK6 != sK6 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_6000]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1,plain,
% 2.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_6859,plain,
% 2.70/0.99      ( m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ r1_tarski(k1_tops_1(sK5,sK8),u1_struct_0(sK5)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_0,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4718,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,k1_tops_1(sK5,sK7))
% 2.70/0.99      | r1_tarski(X0,u1_struct_0(sK5))
% 2.70/0.99      | ~ r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5783,plain,
% 2.70/0.99      ( ~ r1_tarski(k1_tops_1(sK5,sK8),k1_tops_1(sK5,sK7))
% 2.70/0.99      | r1_tarski(k1_tops_1(sK5,sK8),u1_struct_0(sK5))
% 2.70/0.99      | ~ r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_4718]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ r1_tarski(X0,X2)
% 2.70/0.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.70/0.99      | ~ l1_pre_topc(X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_31,negated_conjecture,
% 2.70/0.99      ( l1_pre_topc(sK5) ),
% 2.70/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_744,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ r1_tarski(X0,X2)
% 2.70/0.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.70/0.99      | sK5 != X1 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_31]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_745,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ r1_tarski(X0,X1)
% 2.70/0.99      | r1_tarski(k1_tops_1(sK5,X0),k1_tops_1(sK5,X1)) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_744]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4784,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | r1_tarski(k1_tops_1(sK5,sK8),k1_tops_1(sK5,X0))
% 2.70/0.99      | ~ r1_tarski(sK8,X0) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_745]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5013,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | r1_tarski(k1_tops_1(sK5,sK8),k1_tops_1(sK5,sK7))
% 2.70/0.99      | ~ r1_tarski(sK8,sK7) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_4784]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_7,plain,
% 2.70/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ v2_pre_topc(X3)
% 2.70/0.99      | ~ l1_pre_topc(X3)
% 2.70/0.99      | ~ l1_pre_topc(X1)
% 2.70/0.99      | k1_tops_1(X1,X0) = X0 ),
% 2.70/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_32,negated_conjecture,
% 2.70/0.99      ( v2_pre_topc(sK5) ),
% 2.70/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_645,plain,
% 2.70/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.70/0.99      | ~ l1_pre_topc(X1)
% 2.70/0.99      | ~ l1_pre_topc(X3)
% 2.70/0.99      | k1_tops_1(X1,X0) = X0
% 2.70/0.99      | sK5 != X3 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_32]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_646,plain,
% 2.70/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ l1_pre_topc(X1)
% 2.70/0.99      | ~ l1_pre_topc(sK5)
% 2.70/0.99      | k1_tops_1(X1,X0) = X0 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_645]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_650,plain,
% 2.70/0.99      ( ~ l1_pre_topc(X1)
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ v3_pre_topc(X0,X1)
% 2.70/0.99      | k1_tops_1(X1,X0) = X0 ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_646,c_31]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_651,plain,
% 2.70/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ l1_pre_topc(X1)
% 2.70/0.99      | k1_tops_1(X1,X0) = X0 ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_650]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_726,plain,
% 2.70/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | k1_tops_1(X1,X0) = X0
% 2.70/0.99      | sK5 != X1 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_651,c_31]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_727,plain,
% 2.70/0.99      ( ~ v3_pre_topc(X0,sK5)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | k1_tops_1(sK5,X0) = X0 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_726]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3033,plain,
% 2.70/0.99      ( ~ v3_pre_topc(X0,sK5)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | k1_tops_1(sK5,X0) = X0
% 2.70/0.99      | ~ sP2_iProver_split ),
% 2.70/0.99      inference(splitting,
% 2.70/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.70/0.99                [c_727]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_6,plain,
% 2.70/0.99      ( v3_pre_topc(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.70/0.99      | ~ v2_pre_topc(X1)
% 2.70/0.99      | ~ l1_pre_topc(X1)
% 2.70/0.99      | ~ l1_pre_topc(X3)
% 2.70/0.99      | k1_tops_1(X1,X0) != X0 ),
% 2.70/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_620,plain,
% 2.70/0.99      ( v3_pre_topc(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.70/0.99      | ~ l1_pre_topc(X1)
% 2.70/0.99      | ~ l1_pre_topc(X3)
% 2.70/0.99      | k1_tops_1(X1,X0) != X0
% 2.70/0.99      | sK5 != X1 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_32]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_621,plain,
% 2.70/0.99      ( v3_pre_topc(X0,sK5)
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ l1_pre_topc(X2)
% 2.70/0.99      | ~ l1_pre_topc(sK5)
% 2.70/0.99      | k1_tops_1(sK5,X0) != X0 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_620]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_625,plain,
% 2.70/0.99      ( ~ l1_pre_topc(X2)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.70/0.99      | v3_pre_topc(X0,sK5)
% 2.70/0.99      | k1_tops_1(sK5,X0) != X0 ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_621,c_31]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_626,plain,
% 2.70/0.99      ( v3_pre_topc(X0,sK5)
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ l1_pre_topc(X2)
% 2.70/0.99      | k1_tops_1(sK5,X0) != X0 ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_625]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_774,plain,
% 2.70/0.99      ( v3_pre_topc(X0,sK5)
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | k1_tops_1(sK5,X0) != X0
% 2.70/0.99      | sK5 != X2 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_626,c_31]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_775,plain,
% 2.70/0.99      ( v3_pre_topc(X0,sK5)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | k1_tops_1(sK5,X0) != X0 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_774]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3030,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ sP0_iProver_split ),
% 2.70/0.99      inference(splitting,
% 2.70/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.70/0.99                [c_775]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3034,plain,
% 2.70/0.99      ( sP2_iProver_split | sP0_iProver_split ),
% 2.70/0.99      inference(splitting,
% 2.70/0.99                [splitting(split),new_symbols(definition,[])],
% 2.70/0.99                [c_727]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3158,plain,
% 2.70/0.99      ( k1_tops_1(sK5,X0) = X0
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ v3_pre_topc(X0,sK5) ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_3033,c_3030,c_3034]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3159,plain,
% 2.70/0.99      ( ~ v3_pre_topc(X0,sK5)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | k1_tops_1(sK5,X0) = X0 ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_3158]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4834,plain,
% 2.70/0.99      ( ~ v3_pre_topc(sK8,sK5)
% 2.70/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | k1_tops_1(sK5,sK8) = sK8 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_3159]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3,plain,
% 2.70/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.70/0.99      | ~ v2_pre_topc(X0)
% 2.70/0.99      | ~ l1_pre_topc(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_602,plain,
% 2.70/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.70/0.99      | ~ l1_pre_topc(X0)
% 2.70/0.99      | sK5 != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_32]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_603,plain,
% 2.70/0.99      ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ l1_pre_topc(sK5) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_602]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_607,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | v3_pre_topc(k1_tops_1(sK5,X0),sK5) ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_603,c_31]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_608,plain,
% 2.70/0.99      ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_607]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4787,plain,
% 2.70/0.99      ( v3_pre_topc(k1_tops_1(sK5,sK8),sK5)
% 2.70/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_608]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4719,plain,
% 2.70/0.99      ( m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/0.99      | ~ r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4203,plain,
% 2.70/1.00      ( r1_tarski(X0,u1_struct_0(sK5))
% 2.70/1.00      | ~ r1_tarski(X0,sK7)
% 2.70/1.00      | ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4413,plain,
% 2.70/1.00      ( r1_tarski(k1_tops_1(sK5,sK7),u1_struct_0(sK5))
% 2.70/1.00      | ~ r1_tarski(k1_tops_1(sK5,sK7),sK7)
% 2.70/1.00      | ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_4203]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_9,plain,
% 2.70/1.00      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ v3_pre_topc(X1,X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_20,plain,
% 2.70/1.00      ( sP1(X0,X1)
% 2.70/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.70/1.00      | ~ v2_pre_topc(X0)
% 2.70/1.00      | ~ l1_pre_topc(X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_584,plain,
% 2.70/1.00      ( sP1(X0,X1)
% 2.70/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.70/1.00      | ~ l1_pre_topc(X0)
% 2.70/1.00      | sK5 != X0 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_585,plain,
% 2.70/1.00      ( sP1(sK5,X0)
% 2.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | ~ l1_pre_topc(sK5) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_584]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_589,plain,
% 2.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | sP1(sK5,X0) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_585,c_31]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_590,plain,
% 2.70/1.00      ( sP1(sK5,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.70/1.00      inference(renaming,[status(thm)],[c_589]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_688,plain,
% 2.70/1.00      ( sP0(X0,X1)
% 2.70/1.00      | ~ v3_pre_topc(X0,X1)
% 2.70/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | X2 != X0
% 2.70/1.00      | sK5 != X1 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_590]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_689,plain,
% 2.70/1.00      ( sP0(X0,sK5)
% 2.70/1.00      | ~ v3_pre_topc(X0,sK5)
% 2.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_688]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4286,plain,
% 2.70/1.00      ( sP0(k1_tops_1(sK5,sK7),sK5)
% 2.70/1.00      | ~ v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
% 2.70/1.00      | ~ m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_689]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3036,plain,( X0 = X0 ),theory(equality) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4237,plain,
% 2.70/1.00      ( sK6 = sK6 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_3036]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2,plain,
% 2.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.70/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4107,plain,
% 2.70/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | r1_tarski(sK7,u1_struct_0(sK5)) ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_24,negated_conjecture,
% 2.70/1.00      ( ~ m1_connsp_2(sK7,sK5,sK6)
% 2.70/1.00      | ~ r2_hidden(sK6,X0)
% 2.70/1.00      | ~ v3_pre_topc(X0,sK5)
% 2.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | ~ r1_tarski(X0,sK7) ),
% 2.70/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_21,plain,
% 2.70/1.00      ( m1_connsp_2(X0,X1,X2)
% 2.70/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.70/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.00      | v2_struct_0(X1)
% 2.70/1.00      | ~ v2_pre_topc(X1)
% 2.70/1.00      | ~ l1_pre_topc(X1) ),
% 2.70/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_33,negated_conjecture,
% 2.70/1.00      ( ~ v2_struct_0(sK5) ),
% 2.70/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_547,plain,
% 2.70/1.00      ( m1_connsp_2(X0,X1,X2)
% 2.70/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.70/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.00      | ~ v2_pre_topc(X1)
% 2.70/1.00      | ~ l1_pre_topc(X1)
% 2.70/1.00      | sK5 != X1 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_548,plain,
% 2.70/1.00      ( m1_connsp_2(X0,sK5,X1)
% 2.70/1.00      | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 2.70/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | ~ v2_pre_topc(sK5)
% 2.70/1.00      | ~ l1_pre_topc(sK5) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_547]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_552,plain,
% 2.70/1.00      ( m1_connsp_2(X0,sK5,X1)
% 2.70/1.00      | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 2.70/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_548,c_32,c_31]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_956,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,k1_tops_1(sK5,X1))
% 2.70/1.00      | ~ r2_hidden(sK6,X2)
% 2.70/1.00      | ~ v3_pre_topc(X2,sK5)
% 2.70/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.70/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | ~ r1_tarski(X2,sK7)
% 2.70/1.00      | sK5 != sK5
% 2.70/1.00      | sK7 != X1
% 2.70/1.00      | sK6 != X0 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_552]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_957,plain,
% 2.70/1.00      ( ~ r2_hidden(sK6,X0)
% 2.70/1.00      | ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 2.70/1.00      | ~ v3_pre_topc(X0,sK5)
% 2.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 2.70/1.00      | ~ r1_tarski(X0,sK7) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_956]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_30,negated_conjecture,
% 2.70/1.00      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 2.70/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_29,negated_conjecture,
% 2.70/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.70/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_961,plain,
% 2.70/1.00      ( ~ r2_hidden(sK6,X0)
% 2.70/1.00      | ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 2.70/1.00      | ~ v3_pre_topc(X0,sK5)
% 2.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | ~ r1_tarski(X0,sK7) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_957,c_30,c_29]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4093,plain,
% 2.70/1.00      ( ~ r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 2.70/1.00      | ~ v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
% 2.70/1.00      | ~ m1_subset_1(k1_tops_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | ~ r1_tarski(k1_tops_1(sK5,sK7),sK7) ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_961]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4,plain,
% 2.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.70/1.00      | ~ l1_pre_topc(X1) ),
% 2.70/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_762,plain,
% 2.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.70/1.00      | sK5 != X1 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_31]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_763,plain,
% 2.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | r1_tarski(k1_tops_1(sK5,X0),X0) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_762]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4074,plain,
% 2.70/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | r1_tarski(k1_tops_1(sK5,sK7),sK7) ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_763]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4071,plain,
% 2.70/1.00      ( v3_pre_topc(k1_tops_1(sK5,sK7),sK5)
% 2.70/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_608]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_25,negated_conjecture,
% 2.70/1.00      ( m1_connsp_2(sK7,sK5,sK6) | r2_hidden(sK6,sK8) ),
% 2.70/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_22,plain,
% 2.70/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.70/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.70/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.00      | v2_struct_0(X1)
% 2.70/1.00      | ~ v2_pre_topc(X1)
% 2.70/1.00      | ~ l1_pre_topc(X1) ),
% 2.70/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_23,plain,
% 2.70/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.70/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.70/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.00      | v2_struct_0(X1)
% 2.70/1.00      | ~ v2_pre_topc(X1)
% 2.70/1.00      | ~ l1_pre_topc(X1) ),
% 2.70/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_194,plain,
% 2.70/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.70/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.70/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 2.70/1.00      | v2_struct_0(X1)
% 2.70/1.00      | ~ v2_pre_topc(X1)
% 2.70/1.00      | ~ l1_pre_topc(X1) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_22,c_23]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_195,plain,
% 2.70/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.70/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.70/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.70/1.00      | v2_struct_0(X1)
% 2.70/1.00      | ~ v2_pre_topc(X1)
% 2.70/1.00      | ~ l1_pre_topc(X1) ),
% 2.70/1.00      inference(renaming,[status(thm)],[c_194]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_505,plain,
% 2.70/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.70/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.70/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.70/1.00      | ~ v2_pre_topc(X1)
% 2.70/1.00      | ~ l1_pre_topc(X1)
% 2.70/1.00      | sK5 != X1 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_195,c_33]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_506,plain,
% 2.70/1.00      ( ~ m1_connsp_2(X0,sK5,X1)
% 2.70/1.00      | r2_hidden(X1,k1_tops_1(sK5,X0))
% 2.70/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.70/1.00      | ~ v2_pre_topc(sK5)
% 2.70/1.00      | ~ l1_pre_topc(sK5) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_505]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_510,plain,
% 2.70/1.00      ( ~ m1_connsp_2(X0,sK5,X1)
% 2.70/1.00      | r2_hidden(X1,k1_tops_1(sK5,X0))
% 2.70/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_506,c_32,c_31]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_942,plain,
% 2.70/1.00      ( r2_hidden(X0,k1_tops_1(sK5,X1))
% 2.70/1.00      | r2_hidden(sK6,sK8)
% 2.70/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.70/1.00      | sK5 != sK5
% 2.70/1.00      | sK7 != X1
% 2.70/1.00      | sK6 != X0 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_510]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_943,plain,
% 2.70/1.00      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 2.70/1.00      | r2_hidden(sK6,sK8)
% 2.70/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_942]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_945,plain,
% 2.70/1.00      ( r2_hidden(sK6,sK8) | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_943,c_30]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_946,plain,
% 2.70/1.00      ( r2_hidden(sK6,k1_tops_1(sK5,sK7)) | r2_hidden(sK6,sK8) ),
% 2.70/1.00      inference(renaming,[status(thm)],[c_945]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_26,negated_conjecture,
% 2.70/1.00      ( m1_connsp_2(sK7,sK5,sK6) | r1_tarski(sK8,sK7) ),
% 2.70/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_926,plain,
% 2.70/1.00      ( r2_hidden(X0,k1_tops_1(sK5,X1))
% 2.70/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.70/1.00      | r1_tarski(sK8,sK7)
% 2.70/1.00      | sK5 != sK5
% 2.70/1.00      | sK7 != X1
% 2.70/1.00      | sK6 != X0 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_510]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_927,plain,
% 2.70/1.00      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 2.70/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 2.70/1.00      | r1_tarski(sK8,sK7) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_926]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_929,plain,
% 2.70/1.00      ( r2_hidden(sK6,k1_tops_1(sK5,sK7)) | r1_tarski(sK8,sK7) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_927,c_30]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_27,negated_conjecture,
% 2.70/1.00      ( m1_connsp_2(sK7,sK5,sK6) | v3_pre_topc(sK8,sK5) ),
% 2.70/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_910,plain,
% 2.70/1.00      ( r2_hidden(X0,k1_tops_1(sK5,X1))
% 2.70/1.00      | v3_pre_topc(sK8,sK5)
% 2.70/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.70/1.00      | sK5 != sK5
% 2.70/1.00      | sK7 != X1
% 2.70/1.00      | sK6 != X0 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_510]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_911,plain,
% 2.70/1.00      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 2.70/1.00      | v3_pre_topc(sK8,sK5)
% 2.70/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_910]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_913,plain,
% 2.70/1.00      ( v3_pre_topc(sK8,sK5) | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_911,c_30]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_914,plain,
% 2.70/1.00      ( r2_hidden(sK6,k1_tops_1(sK5,sK7)) | v3_pre_topc(sK8,sK5) ),
% 2.70/1.00      inference(renaming,[status(thm)],[c_913]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_28,negated_conjecture,
% 2.70/1.00      ( m1_connsp_2(sK7,sK5,sK6)
% 2.70/1.00      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.70/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_894,plain,
% 2.70/1.00      ( r2_hidden(X0,k1_tops_1(sK5,X1))
% 2.70/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.70/1.00      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | sK5 != sK5
% 2.70/1.00      | sK7 != X1
% 2.70/1.00      | sK6 != X0 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_510]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_895,plain,
% 2.70/1.00      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 2.70/1.00      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_894]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_897,plain,
% 2.70/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.70/1.00      | r2_hidden(sK6,k1_tops_1(sK5,sK7)) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_895,c_30]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_898,plain,
% 2.70/1.00      ( r2_hidden(sK6,k1_tops_1(sK5,sK7))
% 2.70/1.00      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.70/1.00      inference(renaming,[status(thm)],[c_897]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(contradiction,plain,
% 2.70/1.00      ( $false ),
% 2.70/1.00      inference(minisat,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_15157,c_7363,c_6859,c_5783,c_5013,c_4834,c_4787,
% 2.70/1.00                 c_4719,c_4413,c_4286,c_4237,c_4107,c_4093,c_4074,c_4071,
% 2.70/1.00                 c_946,c_929,c_914,c_898,c_29]) ).
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/1.00  
% 2.70/1.00  ------                               Statistics
% 2.70/1.00  
% 2.70/1.00  ------ General
% 2.70/1.00  
% 2.70/1.00  abstr_ref_over_cycles:                  0
% 2.70/1.00  abstr_ref_under_cycles:                 0
% 2.70/1.00  gc_basic_clause_elim:                   0
% 2.70/1.00  forced_gc_time:                         0
% 2.70/1.00  parsing_time:                           0.008
% 2.70/1.00  unif_index_cands_time:                  0.
% 2.70/1.00  unif_index_add_time:                    0.
% 2.70/1.00  orderings_time:                         0.
% 2.70/1.00  out_proof_time:                         0.009
% 2.70/1.00  total_time:                             0.365
% 2.70/1.00  num_of_symbols:                         54
% 2.70/1.00  num_of_terms:                           6726
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing
% 2.70/1.00  
% 2.70/1.00  num_of_splits:                          4
% 2.70/1.00  num_of_split_atoms:                     3
% 2.70/1.00  num_of_reused_defs:                     1
% 2.70/1.00  num_eq_ax_congr_red:                    29
% 2.70/1.00  num_of_sem_filtered_clauses:            4
% 2.70/1.00  num_of_subtypes:                        0
% 2.70/1.00  monotx_restored_types:                  0
% 2.70/1.00  sat_num_of_epr_types:                   0
% 2.70/1.00  sat_num_of_non_cyclic_types:            0
% 2.70/1.00  sat_guarded_non_collapsed_types:        0
% 2.70/1.00  num_pure_diseq_elim:                    0
% 2.70/1.00  simp_replaced_by:                       0
% 2.70/1.00  res_preprocessed:                       151
% 2.70/1.00  prep_upred:                             0
% 2.70/1.00  prep_unflattend:                        173
% 2.70/1.00  smt_new_axioms:                         0
% 2.70/1.00  pred_elim_cands:                        5
% 2.70/1.00  pred_elim:                              5
% 2.70/1.00  pred_elim_cl:                           3
% 2.70/1.00  pred_elim_cycles:                       8
% 2.70/1.00  merged_defs:                            8
% 2.70/1.00  merged_defs_ncl:                        0
% 2.70/1.00  bin_hyper_res:                          8
% 2.70/1.00  prep_cycles:                            4
% 2.70/1.00  pred_elim_time:                         0.046
% 2.70/1.00  splitting_time:                         0.
% 2.70/1.00  sem_filter_time:                        0.
% 2.70/1.00  monotx_time:                            0.001
% 2.70/1.00  subtype_inf_time:                       0.
% 2.70/1.00  
% 2.70/1.00  ------ Problem properties
% 2.70/1.00  
% 2.70/1.00  clauses:                                35
% 2.70/1.00  conjectures:                            2
% 2.70/1.00  epr:                                    3
% 2.70/1.00  horn:                                   25
% 2.70/1.00  ground:                                 8
% 2.70/1.00  unary:                                  2
% 2.70/1.00  binary:                                 12
% 2.70/1.00  lits:                                   108
% 2.70/1.00  lits_eq:                                2
% 2.70/1.00  fd_pure:                                0
% 2.70/1.00  fd_pseudo:                              0
% 2.70/1.00  fd_cond:                                0
% 2.70/1.00  fd_pseudo_cond:                         0
% 2.70/1.00  ac_symbols:                             0
% 2.70/1.00  
% 2.70/1.00  ------ Propositional Solver
% 2.70/1.00  
% 2.70/1.00  prop_solver_calls:                      30
% 2.70/1.00  prop_fast_solver_calls:                 2111
% 2.70/1.00  smt_solver_calls:                       0
% 2.70/1.00  smt_fast_solver_calls:                  0
% 2.70/1.00  prop_num_of_clauses:                    4134
% 2.70/1.00  prop_preprocess_simplified:             10575
% 2.70/1.00  prop_fo_subsumed:                       93
% 2.70/1.00  prop_solver_time:                       0.
% 2.70/1.00  smt_solver_time:                        0.
% 2.70/1.00  smt_fast_solver_time:                   0.
% 2.70/1.00  prop_fast_solver_time:                  0.
% 2.70/1.00  prop_unsat_core_time:                   0.
% 2.70/1.00  
% 2.70/1.00  ------ QBF
% 2.70/1.00  
% 2.70/1.00  qbf_q_res:                              0
% 2.70/1.00  qbf_num_tautologies:                    0
% 2.70/1.00  qbf_prep_cycles:                        0
% 2.70/1.00  
% 2.70/1.00  ------ BMC1
% 2.70/1.00  
% 2.70/1.00  bmc1_current_bound:                     -1
% 2.70/1.00  bmc1_last_solved_bound:                 -1
% 2.70/1.00  bmc1_unsat_core_size:                   -1
% 2.70/1.00  bmc1_unsat_core_parents_size:           -1
% 2.70/1.00  bmc1_merge_next_fun:                    0
% 2.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.70/1.00  
% 2.70/1.00  ------ Instantiation
% 2.70/1.00  
% 2.70/1.00  inst_num_of_clauses:                    1027
% 2.70/1.00  inst_num_in_passive:                    89
% 2.70/1.00  inst_num_in_active:                     625
% 2.70/1.00  inst_num_in_unprocessed:                312
% 2.70/1.00  inst_num_of_loops:                      715
% 2.70/1.00  inst_num_of_learning_restarts:          0
% 2.70/1.00  inst_num_moves_active_passive:          85
% 2.70/1.00  inst_lit_activity:                      0
% 2.70/1.00  inst_lit_activity_moves:                0
% 2.70/1.00  inst_num_tautologies:                   0
% 2.70/1.00  inst_num_prop_implied:                  0
% 2.70/1.00  inst_num_existing_simplified:           0
% 2.70/1.00  inst_num_eq_res_simplified:             0
% 2.70/1.00  inst_num_child_elim:                    0
% 2.70/1.00  inst_num_of_dismatching_blockings:      117
% 2.70/1.00  inst_num_of_non_proper_insts:           1004
% 2.70/1.00  inst_num_of_duplicates:                 0
% 2.70/1.00  inst_inst_num_from_inst_to_res:         0
% 2.70/1.00  inst_dismatching_checking_time:         0.
% 2.70/1.00  
% 2.70/1.00  ------ Resolution
% 2.70/1.00  
% 2.70/1.00  res_num_of_clauses:                     0
% 2.70/1.00  res_num_in_passive:                     0
% 2.70/1.00  res_num_in_active:                      0
% 2.70/1.00  res_num_of_loops:                       155
% 2.70/1.00  res_forward_subset_subsumed:            64
% 2.70/1.00  res_backward_subset_subsumed:           2
% 2.70/1.00  res_forward_subsumed:                   0
% 2.70/1.00  res_backward_subsumed:                  0
% 2.70/1.00  res_forward_subsumption_resolution:     0
% 2.70/1.00  res_backward_subsumption_resolution:    0
% 2.70/1.00  res_clause_to_clause_subsumption:       3217
% 2.70/1.00  res_orphan_elimination:                 0
% 2.70/1.00  res_tautology_del:                      173
% 2.70/1.00  res_num_eq_res_simplified:              0
% 2.70/1.00  res_num_sel_changes:                    0
% 2.70/1.00  res_moves_from_active_to_pass:          0
% 2.70/1.00  
% 2.70/1.00  ------ Superposition
% 2.70/1.00  
% 2.70/1.00  sup_time_total:                         0.
% 2.70/1.00  sup_time_generating:                    0.
% 2.70/1.00  sup_time_sim_full:                      0.
% 2.70/1.00  sup_time_sim_immed:                     0.
% 2.70/1.00  
% 2.70/1.00  sup_num_of_clauses:                     379
% 2.70/1.00  sup_num_in_active:                      139
% 2.70/1.00  sup_num_in_passive:                     240
% 2.70/1.00  sup_num_of_loops:                       142
% 2.70/1.00  sup_fw_superposition:                   412
% 2.70/1.00  sup_bw_superposition:                   331
% 2.70/1.00  sup_immediate_simplified:               292
% 2.70/1.00  sup_given_eliminated:                   0
% 2.70/1.00  comparisons_done:                       0
% 2.70/1.00  comparisons_avoided:                    0
% 2.70/1.00  
% 2.70/1.00  ------ Simplifications
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  sim_fw_subset_subsumed:                 188
% 2.70/1.00  sim_bw_subset_subsumed:                 5
% 2.70/1.00  sim_fw_subsumed:                        91
% 2.70/1.00  sim_bw_subsumed:                        1
% 2.70/1.00  sim_fw_subsumption_res:                 5
% 2.70/1.00  sim_bw_subsumption_res:                 0
% 2.70/1.00  sim_tautology_del:                      54
% 2.70/1.00  sim_eq_tautology_del:                   0
% 2.70/1.00  sim_eq_res_simp:                        0
% 2.70/1.00  sim_fw_demodulated:                     0
% 2.70/1.00  sim_bw_demodulated:                     2
% 2.70/1.00  sim_light_normalised:                   19
% 2.70/1.00  sim_joinable_taut:                      0
% 2.70/1.00  sim_joinable_simp:                      0
% 2.70/1.00  sim_ac_normalised:                      0
% 2.70/1.00  sim_smt_subsumption:                    0
% 2.70/1.00  
%------------------------------------------------------------------------------
