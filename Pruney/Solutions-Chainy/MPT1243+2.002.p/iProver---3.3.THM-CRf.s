%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:03 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 687 expanded)
%              Number of clauses        :   96 ( 182 expanded)
%              Number of leaves         :   14 ( 183 expanded)
%              Depth                    :   24
%              Number of atoms          :  637 (4917 expanded)
%              Number of equality atoms :  178 ( 328 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> sP0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f15,f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ sP0(X1,X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( sP0(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ sP0(X1,X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( sP0(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ sP0(X1,X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( sP0(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ sP0(sK6,X0)
          | ~ v3_pre_topc(sK6,X0) )
        & ( sP0(sK6,X0)
          | v3_pre_topc(sK6,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ sP0(X1,X0)
              | ~ v3_pre_topc(X1,X0) )
            & ( sP0(X1,X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ sP0(X1,sK5)
            | ~ v3_pre_topc(X1,sK5) )
          & ( sP0(X1,sK5)
            | v3_pre_topc(X1,sK5) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ sP0(sK6,sK5)
      | ~ v3_pre_topc(sK6,sK5) )
    & ( sP0(sK6,sK5)
      | v3_pre_topc(sK6,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f33,f32])).

fof(f56,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f34])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r1_tarski(sK4(X0,X1,X5),X0)
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f12,plain,(
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

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0,X5,X1] :
      ( v3_pre_topc(sK4(X0,X1,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK4(X0,X1,X5))
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,
    ( sP0(sK6,sK5)
    | v3_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X3)
      | ~ r1_tarski(X3,X0)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,
    ( ~ sP0(sK6,sK5)
    | ~ v3_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_tarski(sK3(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2957,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2941,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r1_tarski(sK4(X0,X1,X2),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2946,plain,
    ( sP0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r1_tarski(sK4(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2944,plain,
    ( sP0(X0,X1) != iProver_top
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(X0,sK5)
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK5,X1)) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_2939,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(X0,sK5) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK5,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_3609,plain,
    ( sP0(X0,sK5) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(sK4(X0,sK5,X2),sK5) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r1_tarski(sK4(X0,sK5,X2),X1) != iProver_top
    | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2944,c_2939])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1)
    | v3_pre_topc(sK4(X0,X1,X2),X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_559,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X4,X0)
    | ~ r1_tarski(X3,X2)
    | r1_tarski(X3,k1_tops_1(sK5,X2))
    | sK4(X0,X1,X4) != X3
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_328])).

cnf(c_560,plain,
    ( ~ sP0(X0,sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK4(X0,sK5,X2),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X2,X0)
    | ~ r1_tarski(sK4(X0,sK5,X2),X1)
    | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_576,plain,
    ( ~ sP0(X0,sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X2,X0)
    | ~ r1_tarski(sK4(X0,sK5,X2),X1)
    | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_560,c_18])).

cnf(c_582,plain,
    ( sP0(X0,sK5) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r1_tarski(sK4(X0,sK5,X2),X1) != iProver_top
    | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_4144,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | sP0(X0,sK5) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r1_tarski(sK4(X0,sK5,X2),X1) != iProver_top
    | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3609,c_582])).

cnf(c_4145,plain,
    ( sP0(X0,sK5) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r1_tarski(sK4(X0,sK5,X2),X1) != iProver_top
    | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4144])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,sK4(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2947,plain,
    ( sP0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,sK4(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2956,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3896,plain,
    ( sP0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | r1_tarski(sK4(X0,X1,X2),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2947,c_2956])).

cnf(c_6599,plain,
    ( sP0(X0,sK5) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_tops_1(sK5,X1)) = iProver_top
    | r1_tarski(sK4(X0,sK5,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4145,c_3896])).

cnf(c_10127,plain,
    ( sP0(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2946,c_6599])).

cnf(c_10289,plain,
    ( sP0(sK6,sK5) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK5,sK6)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2941,c_10127])).

cnf(c_20,negated_conjecture,
    ( sP0(sK6,sK5)
    | v3_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,plain,
    ( sP0(sK6,sK5) = iProver_top
    | v3_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2949,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(sK2(X0,X1),X2)
    | ~ r2_hidden(sK2(X0,X1),X0)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2953,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_pre_topc(X2,X1) != iProver_top
    | r2_hidden(sK2(X0,X1),X0) != iProver_top
    | r2_hidden(sK2(X0,X1),X2) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3063,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_pre_topc(X2,X1) != iProver_top
    | r2_hidden(sK2(X0,X1),X2) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2953,c_2956])).

cnf(c_5477,plain,
    ( sP0(X0,sK5) = iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top
    | r2_hidden(sK2(X0,sK5),sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2941,c_3063])).

cnf(c_5666,plain,
    ( sP0(sK6,sK5) = iProver_top
    | m1_subset_1(sK3(sK6,sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2949,c_5477])).

cnf(c_26,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( ~ sP0(sK6,sK5)
    | ~ v3_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,plain,
    ( sP0(sK6,sK5) != iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4237,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4242,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4237])).

cnf(c_4746,plain,
    ( sP0(X0,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK6,sK5)
    | ~ r2_hidden(sK2(X0,sK5),X0)
    | ~ r2_hidden(sK2(X0,sK5),sK6)
    | ~ r1_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4766,plain,
    ( sP0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK6,sK5)
    | ~ r2_hidden(sK2(sK6,sK5),sK6)
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_4746])).

cnf(c_4767,plain,
    ( sP0(sK6,sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top
    | r2_hidden(sK2(sK6,sK5),sK6) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4766])).

cnf(c_5216,plain,
    ( sP0(sK6,sK5)
    | m1_subset_1(sK3(sK6,sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK2(sK6,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5223,plain,
    ( sP0(sK6,sK5) = iProver_top
    | m1_subset_1(sK3(sK6,sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r2_hidden(sK2(sK6,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5216])).

cnf(c_5950,plain,
    ( v3_pre_topc(sK6,sK5) != iProver_top
    | m1_subset_1(sK3(sK6,sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5666,c_26,c_28,c_4242,c_4767,c_5223])).

cnf(c_5951,plain,
    ( m1_subset_1(sK3(sK6,sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_5950])).

cnf(c_3210,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2941,c_2939])).

cnf(c_5957,plain,
    ( v3_pre_topc(sK6,sK5) != iProver_top
    | r1_tarski(sK6,sK3(sK6,sK5)) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK5,sK3(sK6,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5951,c_3210])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2955,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6270,plain,
    ( k1_tops_1(sK5,sK3(sK6,sK5)) = sK6
    | v3_pre_topc(sK6,sK5) != iProver_top
    | r1_tarski(k1_tops_1(sK5,sK3(sK6,sK5)),sK6) != iProver_top
    | r1_tarski(sK6,sK3(sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5957,c_2955])).

cnf(c_11,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2951,plain,
    ( sP0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r1_tarski(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5667,plain,
    ( sP0(sK6,sK5) = iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top
    | r1_tarski(sK3(sK6,sK5),sK6) = iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2951,c_5477])).

cnf(c_5822,plain,
    ( r1_tarski(sK3(sK6,sK5),sK6) = iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5667,c_28,c_4242])).

cnf(c_5823,plain,
    ( v3_pre_topc(sK6,sK5) != iProver_top
    | r1_tarski(sK3(sK6,sK5),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_5822])).

cnf(c_10,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0)
    | r2_hidden(sK2(X0,X1),sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2952,plain,
    ( sP0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK2(X0,X1),sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4472,plain,
    ( sP0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK2(X0,X1),X2) = iProver_top
    | r1_tarski(sK3(X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2952,c_2956])).

cnf(c_8202,plain,
    ( sP0(sK6,sK5) = iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top
    | r2_hidden(sK2(sK6,sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5823,c_4472])).

cnf(c_8721,plain,
    ( v3_pre_topc(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6270,c_26,c_28,c_4242,c_4767,c_8202])).

cnf(c_10340,plain,
    ( r2_hidden(X0,k1_tops_1(sK5,sK6)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10289,c_26,c_27,c_28,c_4242,c_4767,c_8202])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2958,plain,
    ( r2_hidden(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10348,plain,
    ( r2_hidden(sK1(X0,k1_tops_1(sK5,sK6)),sK6) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10340,c_2958])).

cnf(c_10533,plain,
    ( r1_tarski(sK6,k1_tops_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2957,c_10348])).

cnf(c_2427,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3148,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k1_tops_1(sK5,sK6),sK5)
    | X0 != k1_tops_1(sK5,sK6)
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(c_3410,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK5,sK6),sK5)
    | v3_pre_topc(sK6,X0)
    | X0 != sK5
    | sK6 != k1_tops_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3148])).

cnf(c_3412,plain,
    ( X0 != sK5
    | sK6 != k1_tops_1(sK5,sK6)
    | v3_pre_topc(k1_tops_1(sK5,sK6),sK5) != iProver_top
    | v3_pre_topc(sK6,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3410])).

cnf(c_3414,plain,
    ( sK5 != sK5
    | sK6 != k1_tops_1(sK5,sK6)
    | v3_pre_topc(k1_tops_1(sK5,sK6),sK5) != iProver_top
    | v3_pre_topc(sK6,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3412])).

cnf(c_3214,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK5,sK6))
    | ~ r1_tarski(k1_tops_1(sK5,sK6),X0)
    | X0 = k1_tops_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3344,plain,
    ( ~ r1_tarski(k1_tops_1(sK5,sK6),sK6)
    | ~ r1_tarski(sK6,k1_tops_1(sK5,sK6))
    | sK6 = k1_tops_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3214])).

cnf(c_3347,plain,
    ( sK6 = k1_tops_1(sK5,sK6)
    | r1_tarski(k1_tops_1(sK5,sK6),sK6) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3344])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,X0),X0) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_3118,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_3119,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(k1_tops_1(sK5,sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3118])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(k1_tops_1(X1,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(k1_tops_1(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(k1_tops_1(sK5,X0),sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_311,plain,
    ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_22])).

cnf(c_312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(k1_tops_1(sK5,X0),sK5) ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_3115,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(k1_tops_1(sK5,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_3116,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(k1_tops_1(sK5,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3115])).

cnf(c_71,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_67,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10533,c_8721,c_3414,c_3347,c_3119,c_3116,c_71,c_67,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:58:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.60/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.02  
% 3.60/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/1.02  
% 3.60/1.02  ------  iProver source info
% 3.60/1.02  
% 3.60/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.60/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/1.02  git: non_committed_changes: false
% 3.60/1.02  git: last_make_outside_of_git: false
% 3.60/1.02  
% 3.60/1.02  ------ 
% 3.60/1.02  
% 3.60/1.02  ------ Input Options
% 3.60/1.02  
% 3.60/1.02  --out_options                           all
% 3.60/1.02  --tptp_safe_out                         true
% 3.60/1.02  --problem_path                          ""
% 3.60/1.02  --include_path                          ""
% 3.60/1.02  --clausifier                            res/vclausify_rel
% 3.60/1.02  --clausifier_options                    --mode clausify
% 3.60/1.02  --stdin                                 false
% 3.60/1.02  --stats_out                             all
% 3.60/1.02  
% 3.60/1.02  ------ General Options
% 3.60/1.02  
% 3.60/1.02  --fof                                   false
% 3.60/1.02  --time_out_real                         305.
% 3.60/1.02  --time_out_virtual                      -1.
% 3.60/1.02  --symbol_type_check                     false
% 3.60/1.02  --clausify_out                          false
% 3.60/1.02  --sig_cnt_out                           false
% 3.60/1.02  --trig_cnt_out                          false
% 3.60/1.02  --trig_cnt_out_tolerance                1.
% 3.60/1.02  --trig_cnt_out_sk_spl                   false
% 3.60/1.02  --abstr_cl_out                          false
% 3.60/1.02  
% 3.60/1.02  ------ Global Options
% 3.60/1.02  
% 3.60/1.02  --schedule                              default
% 3.60/1.02  --add_important_lit                     false
% 3.60/1.02  --prop_solver_per_cl                    1000
% 3.60/1.02  --min_unsat_core                        false
% 3.60/1.02  --soft_assumptions                      false
% 3.60/1.02  --soft_lemma_size                       3
% 3.60/1.02  --prop_impl_unit_size                   0
% 3.60/1.02  --prop_impl_unit                        []
% 3.60/1.02  --share_sel_clauses                     true
% 3.60/1.02  --reset_solvers                         false
% 3.60/1.02  --bc_imp_inh                            [conj_cone]
% 3.60/1.02  --conj_cone_tolerance                   3.
% 3.60/1.02  --extra_neg_conj                        none
% 3.60/1.02  --large_theory_mode                     true
% 3.60/1.02  --prolific_symb_bound                   200
% 3.60/1.02  --lt_threshold                          2000
% 3.60/1.02  --clause_weak_htbl                      true
% 3.60/1.02  --gc_record_bc_elim                     false
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing Options
% 3.60/1.02  
% 3.60/1.02  --preprocessing_flag                    true
% 3.60/1.02  --time_out_prep_mult                    0.1
% 3.60/1.02  --splitting_mode                        input
% 3.60/1.02  --splitting_grd                         true
% 3.60/1.02  --splitting_cvd                         false
% 3.60/1.02  --splitting_cvd_svl                     false
% 3.60/1.02  --splitting_nvd                         32
% 3.60/1.02  --sub_typing                            true
% 3.60/1.02  --prep_gs_sim                           true
% 3.60/1.02  --prep_unflatten                        true
% 3.60/1.02  --prep_res_sim                          true
% 3.60/1.02  --prep_upred                            true
% 3.60/1.02  --prep_sem_filter                       exhaustive
% 3.60/1.02  --prep_sem_filter_out                   false
% 3.60/1.02  --pred_elim                             true
% 3.60/1.02  --res_sim_input                         true
% 3.60/1.02  --eq_ax_congr_red                       true
% 3.60/1.02  --pure_diseq_elim                       true
% 3.60/1.02  --brand_transform                       false
% 3.60/1.02  --non_eq_to_eq                          false
% 3.60/1.02  --prep_def_merge                        true
% 3.60/1.02  --prep_def_merge_prop_impl              false
% 3.60/1.02  --prep_def_merge_mbd                    true
% 3.60/1.02  --prep_def_merge_tr_red                 false
% 3.60/1.02  --prep_def_merge_tr_cl                  false
% 3.60/1.02  --smt_preprocessing                     true
% 3.60/1.02  --smt_ac_axioms                         fast
% 3.60/1.02  --preprocessed_out                      false
% 3.60/1.02  --preprocessed_stats                    false
% 3.60/1.02  
% 3.60/1.02  ------ Abstraction refinement Options
% 3.60/1.02  
% 3.60/1.02  --abstr_ref                             []
% 3.60/1.02  --abstr_ref_prep                        false
% 3.60/1.02  --abstr_ref_until_sat                   false
% 3.60/1.02  --abstr_ref_sig_restrict                funpre
% 3.60/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.02  --abstr_ref_under                       []
% 3.60/1.02  
% 3.60/1.02  ------ SAT Options
% 3.60/1.02  
% 3.60/1.02  --sat_mode                              false
% 3.60/1.02  --sat_fm_restart_options                ""
% 3.60/1.02  --sat_gr_def                            false
% 3.60/1.02  --sat_epr_types                         true
% 3.60/1.02  --sat_non_cyclic_types                  false
% 3.60/1.02  --sat_finite_models                     false
% 3.60/1.02  --sat_fm_lemmas                         false
% 3.60/1.02  --sat_fm_prep                           false
% 3.60/1.02  --sat_fm_uc_incr                        true
% 3.60/1.02  --sat_out_model                         small
% 3.60/1.02  --sat_out_clauses                       false
% 3.60/1.02  
% 3.60/1.02  ------ QBF Options
% 3.60/1.02  
% 3.60/1.02  --qbf_mode                              false
% 3.60/1.02  --qbf_elim_univ                         false
% 3.60/1.02  --qbf_dom_inst                          none
% 3.60/1.02  --qbf_dom_pre_inst                      false
% 3.60/1.02  --qbf_sk_in                             false
% 3.60/1.02  --qbf_pred_elim                         true
% 3.60/1.02  --qbf_split                             512
% 3.60/1.02  
% 3.60/1.02  ------ BMC1 Options
% 3.60/1.02  
% 3.60/1.02  --bmc1_incremental                      false
% 3.60/1.02  --bmc1_axioms                           reachable_all
% 3.60/1.02  --bmc1_min_bound                        0
% 3.60/1.02  --bmc1_max_bound                        -1
% 3.60/1.02  --bmc1_max_bound_default                -1
% 3.60/1.02  --bmc1_symbol_reachability              true
% 3.60/1.02  --bmc1_property_lemmas                  false
% 3.60/1.02  --bmc1_k_induction                      false
% 3.60/1.02  --bmc1_non_equiv_states                 false
% 3.60/1.02  --bmc1_deadlock                         false
% 3.60/1.02  --bmc1_ucm                              false
% 3.60/1.02  --bmc1_add_unsat_core                   none
% 3.60/1.02  --bmc1_unsat_core_children              false
% 3.60/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.02  --bmc1_out_stat                         full
% 3.60/1.02  --bmc1_ground_init                      false
% 3.60/1.02  --bmc1_pre_inst_next_state              false
% 3.60/1.02  --bmc1_pre_inst_state                   false
% 3.60/1.02  --bmc1_pre_inst_reach_state             false
% 3.60/1.02  --bmc1_out_unsat_core                   false
% 3.60/1.02  --bmc1_aig_witness_out                  false
% 3.60/1.02  --bmc1_verbose                          false
% 3.60/1.02  --bmc1_dump_clauses_tptp                false
% 3.60/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.02  --bmc1_dump_file                        -
% 3.60/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.02  --bmc1_ucm_extend_mode                  1
% 3.60/1.02  --bmc1_ucm_init_mode                    2
% 3.60/1.02  --bmc1_ucm_cone_mode                    none
% 3.60/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.02  --bmc1_ucm_relax_model                  4
% 3.60/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.02  --bmc1_ucm_layered_model                none
% 3.60/1.02  --bmc1_ucm_max_lemma_size               10
% 3.60/1.02  
% 3.60/1.02  ------ AIG Options
% 3.60/1.02  
% 3.60/1.02  --aig_mode                              false
% 3.60/1.02  
% 3.60/1.02  ------ Instantiation Options
% 3.60/1.02  
% 3.60/1.02  --instantiation_flag                    true
% 3.60/1.02  --inst_sos_flag                         false
% 3.60/1.02  --inst_sos_phase                        true
% 3.60/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.02  --inst_lit_sel_side                     num_symb
% 3.60/1.02  --inst_solver_per_active                1400
% 3.60/1.02  --inst_solver_calls_frac                1.
% 3.60/1.02  --inst_passive_queue_type               priority_queues
% 3.60/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.02  --inst_passive_queues_freq              [25;2]
% 3.60/1.02  --inst_dismatching                      true
% 3.60/1.02  --inst_eager_unprocessed_to_passive     true
% 3.60/1.02  --inst_prop_sim_given                   true
% 3.60/1.02  --inst_prop_sim_new                     false
% 3.60/1.02  --inst_subs_new                         false
% 3.60/1.02  --inst_eq_res_simp                      false
% 3.60/1.02  --inst_subs_given                       false
% 3.60/1.02  --inst_orphan_elimination               true
% 3.60/1.02  --inst_learning_loop_flag               true
% 3.60/1.02  --inst_learning_start                   3000
% 3.60/1.02  --inst_learning_factor                  2
% 3.60/1.02  --inst_start_prop_sim_after_learn       3
% 3.60/1.02  --inst_sel_renew                        solver
% 3.60/1.02  --inst_lit_activity_flag                true
% 3.60/1.02  --inst_restr_to_given                   false
% 3.60/1.02  --inst_activity_threshold               500
% 3.60/1.02  --inst_out_proof                        true
% 3.60/1.02  
% 3.60/1.02  ------ Resolution Options
% 3.60/1.02  
% 3.60/1.02  --resolution_flag                       true
% 3.60/1.02  --res_lit_sel                           adaptive
% 3.60/1.02  --res_lit_sel_side                      none
% 3.60/1.02  --res_ordering                          kbo
% 3.60/1.02  --res_to_prop_solver                    active
% 3.60/1.02  --res_prop_simpl_new                    false
% 3.60/1.02  --res_prop_simpl_given                  true
% 3.60/1.02  --res_passive_queue_type                priority_queues
% 3.60/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.02  --res_passive_queues_freq               [15;5]
% 3.60/1.02  --res_forward_subs                      full
% 3.60/1.02  --res_backward_subs                     full
% 3.60/1.02  --res_forward_subs_resolution           true
% 3.60/1.02  --res_backward_subs_resolution          true
% 3.60/1.02  --res_orphan_elimination                true
% 3.60/1.02  --res_time_limit                        2.
% 3.60/1.02  --res_out_proof                         true
% 3.60/1.02  
% 3.60/1.02  ------ Superposition Options
% 3.60/1.02  
% 3.60/1.02  --superposition_flag                    true
% 3.60/1.02  --sup_passive_queue_type                priority_queues
% 3.60/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.02  --demod_completeness_check              fast
% 3.60/1.02  --demod_use_ground                      true
% 3.60/1.02  --sup_to_prop_solver                    passive
% 3.60/1.02  --sup_prop_simpl_new                    true
% 3.60/1.02  --sup_prop_simpl_given                  true
% 3.60/1.02  --sup_fun_splitting                     false
% 3.60/1.02  --sup_smt_interval                      50000
% 3.60/1.02  
% 3.60/1.02  ------ Superposition Simplification Setup
% 3.60/1.02  
% 3.60/1.02  --sup_indices_passive                   []
% 3.60/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_full_bw                           [BwDemod]
% 3.60/1.02  --sup_immed_triv                        [TrivRules]
% 3.60/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_immed_bw_main                     []
% 3.60/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.02  
% 3.60/1.02  ------ Combination Options
% 3.60/1.02  
% 3.60/1.02  --comb_res_mult                         3
% 3.60/1.02  --comb_sup_mult                         2
% 3.60/1.02  --comb_inst_mult                        10
% 3.60/1.02  
% 3.60/1.02  ------ Debug Options
% 3.60/1.02  
% 3.60/1.02  --dbg_backtrace                         false
% 3.60/1.02  --dbg_dump_prop_clauses                 false
% 3.60/1.02  --dbg_dump_prop_clauses_file            -
% 3.60/1.02  --dbg_out_stat                          false
% 3.60/1.02  ------ Parsing...
% 3.60/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/1.02  ------ Proving...
% 3.60/1.02  ------ Problem Properties 
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  clauses                                 21
% 3.60/1.02  conjectures                             3
% 3.60/1.02  EPR                                     5
% 3.60/1.02  Horn                                    15
% 3.60/1.02  unary                                   2
% 3.60/1.02  binary                                  6
% 3.60/1.02  lits                                    61
% 3.60/1.02  lits eq                                 1
% 3.60/1.02  fd_pure                                 0
% 3.60/1.02  fd_pseudo                               0
% 3.60/1.02  fd_cond                                 0
% 3.60/1.02  fd_pseudo_cond                          1
% 3.60/1.02  AC symbols                              0
% 3.60/1.02  
% 3.60/1.02  ------ Schedule dynamic 5 is on 
% 3.60/1.02  
% 3.60/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  ------ 
% 3.60/1.02  Current options:
% 3.60/1.02  ------ 
% 3.60/1.02  
% 3.60/1.02  ------ Input Options
% 3.60/1.02  
% 3.60/1.02  --out_options                           all
% 3.60/1.02  --tptp_safe_out                         true
% 3.60/1.02  --problem_path                          ""
% 3.60/1.02  --include_path                          ""
% 3.60/1.02  --clausifier                            res/vclausify_rel
% 3.60/1.02  --clausifier_options                    --mode clausify
% 3.60/1.02  --stdin                                 false
% 3.60/1.02  --stats_out                             all
% 3.60/1.02  
% 3.60/1.02  ------ General Options
% 3.60/1.02  
% 3.60/1.02  --fof                                   false
% 3.60/1.02  --time_out_real                         305.
% 3.60/1.02  --time_out_virtual                      -1.
% 3.60/1.02  --symbol_type_check                     false
% 3.60/1.02  --clausify_out                          false
% 3.60/1.02  --sig_cnt_out                           false
% 3.60/1.02  --trig_cnt_out                          false
% 3.60/1.02  --trig_cnt_out_tolerance                1.
% 3.60/1.02  --trig_cnt_out_sk_spl                   false
% 3.60/1.02  --abstr_cl_out                          false
% 3.60/1.02  
% 3.60/1.02  ------ Global Options
% 3.60/1.02  
% 3.60/1.02  --schedule                              default
% 3.60/1.02  --add_important_lit                     false
% 3.60/1.02  --prop_solver_per_cl                    1000
% 3.60/1.02  --min_unsat_core                        false
% 3.60/1.02  --soft_assumptions                      false
% 3.60/1.02  --soft_lemma_size                       3
% 3.60/1.02  --prop_impl_unit_size                   0
% 3.60/1.02  --prop_impl_unit                        []
% 3.60/1.02  --share_sel_clauses                     true
% 3.60/1.02  --reset_solvers                         false
% 3.60/1.02  --bc_imp_inh                            [conj_cone]
% 3.60/1.02  --conj_cone_tolerance                   3.
% 3.60/1.02  --extra_neg_conj                        none
% 3.60/1.02  --large_theory_mode                     true
% 3.60/1.02  --prolific_symb_bound                   200
% 3.60/1.02  --lt_threshold                          2000
% 3.60/1.02  --clause_weak_htbl                      true
% 3.60/1.02  --gc_record_bc_elim                     false
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing Options
% 3.60/1.02  
% 3.60/1.02  --preprocessing_flag                    true
% 3.60/1.02  --time_out_prep_mult                    0.1
% 3.60/1.02  --splitting_mode                        input
% 3.60/1.02  --splitting_grd                         true
% 3.60/1.02  --splitting_cvd                         false
% 3.60/1.02  --splitting_cvd_svl                     false
% 3.60/1.02  --splitting_nvd                         32
% 3.60/1.02  --sub_typing                            true
% 3.60/1.02  --prep_gs_sim                           true
% 3.60/1.02  --prep_unflatten                        true
% 3.60/1.02  --prep_res_sim                          true
% 3.60/1.02  --prep_upred                            true
% 3.60/1.02  --prep_sem_filter                       exhaustive
% 3.60/1.02  --prep_sem_filter_out                   false
% 3.60/1.02  --pred_elim                             true
% 3.60/1.02  --res_sim_input                         true
% 3.60/1.02  --eq_ax_congr_red                       true
% 3.60/1.02  --pure_diseq_elim                       true
% 3.60/1.02  --brand_transform                       false
% 3.60/1.02  --non_eq_to_eq                          false
% 3.60/1.02  --prep_def_merge                        true
% 3.60/1.02  --prep_def_merge_prop_impl              false
% 3.60/1.02  --prep_def_merge_mbd                    true
% 3.60/1.02  --prep_def_merge_tr_red                 false
% 3.60/1.02  --prep_def_merge_tr_cl                  false
% 3.60/1.02  --smt_preprocessing                     true
% 3.60/1.02  --smt_ac_axioms                         fast
% 3.60/1.02  --preprocessed_out                      false
% 3.60/1.02  --preprocessed_stats                    false
% 3.60/1.02  
% 3.60/1.02  ------ Abstraction refinement Options
% 3.60/1.02  
% 3.60/1.02  --abstr_ref                             []
% 3.60/1.02  --abstr_ref_prep                        false
% 3.60/1.02  --abstr_ref_until_sat                   false
% 3.60/1.02  --abstr_ref_sig_restrict                funpre
% 3.60/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.02  --abstr_ref_under                       []
% 3.60/1.02  
% 3.60/1.02  ------ SAT Options
% 3.60/1.02  
% 3.60/1.02  --sat_mode                              false
% 3.60/1.02  --sat_fm_restart_options                ""
% 3.60/1.02  --sat_gr_def                            false
% 3.60/1.02  --sat_epr_types                         true
% 3.60/1.02  --sat_non_cyclic_types                  false
% 3.60/1.02  --sat_finite_models                     false
% 3.60/1.02  --sat_fm_lemmas                         false
% 3.60/1.02  --sat_fm_prep                           false
% 3.60/1.02  --sat_fm_uc_incr                        true
% 3.60/1.02  --sat_out_model                         small
% 3.60/1.02  --sat_out_clauses                       false
% 3.60/1.02  
% 3.60/1.02  ------ QBF Options
% 3.60/1.02  
% 3.60/1.02  --qbf_mode                              false
% 3.60/1.02  --qbf_elim_univ                         false
% 3.60/1.02  --qbf_dom_inst                          none
% 3.60/1.02  --qbf_dom_pre_inst                      false
% 3.60/1.02  --qbf_sk_in                             false
% 3.60/1.02  --qbf_pred_elim                         true
% 3.60/1.02  --qbf_split                             512
% 3.60/1.02  
% 3.60/1.02  ------ BMC1 Options
% 3.60/1.02  
% 3.60/1.02  --bmc1_incremental                      false
% 3.60/1.02  --bmc1_axioms                           reachable_all
% 3.60/1.02  --bmc1_min_bound                        0
% 3.60/1.02  --bmc1_max_bound                        -1
% 3.60/1.02  --bmc1_max_bound_default                -1
% 3.60/1.02  --bmc1_symbol_reachability              true
% 3.60/1.02  --bmc1_property_lemmas                  false
% 3.60/1.02  --bmc1_k_induction                      false
% 3.60/1.02  --bmc1_non_equiv_states                 false
% 3.60/1.02  --bmc1_deadlock                         false
% 3.60/1.02  --bmc1_ucm                              false
% 3.60/1.02  --bmc1_add_unsat_core                   none
% 3.60/1.02  --bmc1_unsat_core_children              false
% 3.60/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.02  --bmc1_out_stat                         full
% 3.60/1.02  --bmc1_ground_init                      false
% 3.60/1.02  --bmc1_pre_inst_next_state              false
% 3.60/1.02  --bmc1_pre_inst_state                   false
% 3.60/1.02  --bmc1_pre_inst_reach_state             false
% 3.60/1.02  --bmc1_out_unsat_core                   false
% 3.60/1.02  --bmc1_aig_witness_out                  false
% 3.60/1.02  --bmc1_verbose                          false
% 3.60/1.02  --bmc1_dump_clauses_tptp                false
% 3.60/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.02  --bmc1_dump_file                        -
% 3.60/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.02  --bmc1_ucm_extend_mode                  1
% 3.60/1.02  --bmc1_ucm_init_mode                    2
% 3.60/1.02  --bmc1_ucm_cone_mode                    none
% 3.60/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.02  --bmc1_ucm_relax_model                  4
% 3.60/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.02  --bmc1_ucm_layered_model                none
% 3.60/1.02  --bmc1_ucm_max_lemma_size               10
% 3.60/1.02  
% 3.60/1.02  ------ AIG Options
% 3.60/1.02  
% 3.60/1.02  --aig_mode                              false
% 3.60/1.02  
% 3.60/1.02  ------ Instantiation Options
% 3.60/1.02  
% 3.60/1.02  --instantiation_flag                    true
% 3.60/1.02  --inst_sos_flag                         false
% 3.60/1.02  --inst_sos_phase                        true
% 3.60/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.02  --inst_lit_sel_side                     none
% 3.60/1.02  --inst_solver_per_active                1400
% 3.60/1.02  --inst_solver_calls_frac                1.
% 3.60/1.02  --inst_passive_queue_type               priority_queues
% 3.60/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.02  --inst_passive_queues_freq              [25;2]
% 3.60/1.02  --inst_dismatching                      true
% 3.60/1.02  --inst_eager_unprocessed_to_passive     true
% 3.60/1.02  --inst_prop_sim_given                   true
% 3.60/1.02  --inst_prop_sim_new                     false
% 3.60/1.02  --inst_subs_new                         false
% 3.60/1.02  --inst_eq_res_simp                      false
% 3.60/1.02  --inst_subs_given                       false
% 3.60/1.02  --inst_orphan_elimination               true
% 3.60/1.02  --inst_learning_loop_flag               true
% 3.60/1.02  --inst_learning_start                   3000
% 3.60/1.02  --inst_learning_factor                  2
% 3.60/1.02  --inst_start_prop_sim_after_learn       3
% 3.60/1.02  --inst_sel_renew                        solver
% 3.60/1.02  --inst_lit_activity_flag                true
% 3.60/1.02  --inst_restr_to_given                   false
% 3.60/1.02  --inst_activity_threshold               500
% 3.60/1.02  --inst_out_proof                        true
% 3.60/1.02  
% 3.60/1.02  ------ Resolution Options
% 3.60/1.02  
% 3.60/1.02  --resolution_flag                       false
% 3.60/1.02  --res_lit_sel                           adaptive
% 3.60/1.02  --res_lit_sel_side                      none
% 3.60/1.02  --res_ordering                          kbo
% 3.60/1.02  --res_to_prop_solver                    active
% 3.60/1.02  --res_prop_simpl_new                    false
% 3.60/1.02  --res_prop_simpl_given                  true
% 3.60/1.02  --res_passive_queue_type                priority_queues
% 3.60/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.02  --res_passive_queues_freq               [15;5]
% 3.60/1.02  --res_forward_subs                      full
% 3.60/1.02  --res_backward_subs                     full
% 3.60/1.02  --res_forward_subs_resolution           true
% 3.60/1.02  --res_backward_subs_resolution          true
% 3.60/1.02  --res_orphan_elimination                true
% 3.60/1.02  --res_time_limit                        2.
% 3.60/1.02  --res_out_proof                         true
% 3.60/1.02  
% 3.60/1.02  ------ Superposition Options
% 3.60/1.02  
% 3.60/1.02  --superposition_flag                    true
% 3.60/1.02  --sup_passive_queue_type                priority_queues
% 3.60/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.02  --demod_completeness_check              fast
% 3.60/1.02  --demod_use_ground                      true
% 3.60/1.02  --sup_to_prop_solver                    passive
% 3.60/1.02  --sup_prop_simpl_new                    true
% 3.60/1.02  --sup_prop_simpl_given                  true
% 3.60/1.02  --sup_fun_splitting                     false
% 3.60/1.02  --sup_smt_interval                      50000
% 3.60/1.02  
% 3.60/1.02  ------ Superposition Simplification Setup
% 3.60/1.02  
% 3.60/1.02  --sup_indices_passive                   []
% 3.60/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_full_bw                           [BwDemod]
% 3.60/1.02  --sup_immed_triv                        [TrivRules]
% 3.60/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_immed_bw_main                     []
% 3.60/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.02  
% 3.60/1.02  ------ Combination Options
% 3.60/1.02  
% 3.60/1.02  --comb_res_mult                         3
% 3.60/1.02  --comb_sup_mult                         2
% 3.60/1.02  --comb_inst_mult                        10
% 3.60/1.02  
% 3.60/1.02  ------ Debug Options
% 3.60/1.02  
% 3.60/1.02  --dbg_backtrace                         false
% 3.60/1.02  --dbg_dump_prop_clauses                 false
% 3.60/1.02  --dbg_dump_prop_clauses_file            -
% 3.60/1.02  --dbg_out_stat                          false
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  ------ Proving...
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  % SZS status Theorem for theBenchmark.p
% 3.60/1.02  
% 3.60/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/1.02  
% 3.60/1.02  fof(f1,axiom,(
% 3.60/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f8,plain,(
% 3.60/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.60/1.02    inference(ennf_transformation,[],[f1])).
% 3.60/1.02  
% 3.60/1.02  fof(f18,plain,(
% 3.60/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.60/1.02    inference(nnf_transformation,[],[f8])).
% 3.60/1.02  
% 3.60/1.02  fof(f19,plain,(
% 3.60/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.60/1.02    inference(rectify,[],[f18])).
% 3.60/1.02  
% 3.60/1.02  fof(f20,plain,(
% 3.60/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.60/1.02    introduced(choice_axiom,[])).
% 3.60/1.02  
% 3.60/1.02  fof(f21,plain,(
% 3.60/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.60/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 3.60/1.02  
% 3.60/1.02  fof(f36,plain,(
% 3.60/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f21])).
% 3.60/1.02  
% 3.60/1.02  fof(f6,conjecture,(
% 3.60/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f7,negated_conjecture,(
% 3.60/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.60/1.02    inference(negated_conjecture,[],[f6])).
% 3.60/1.02  
% 3.60/1.02  fof(f14,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.60/1.02    inference(ennf_transformation,[],[f7])).
% 3.60/1.02  
% 3.60/1.02  fof(f15,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.60/1.02    inference(flattening,[],[f14])).
% 3.60/1.02  
% 3.60/1.02  fof(f16,plain,(
% 3.60/1.02    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.60/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.60/1.02  
% 3.60/1.02  fof(f17,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.60/1.02    inference(definition_folding,[],[f15,f16])).
% 3.60/1.02  
% 3.60/1.02  fof(f30,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : (((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.60/1.02    inference(nnf_transformation,[],[f17])).
% 3.60/1.02  
% 3.60/1.02  fof(f31,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : ((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.60/1.02    inference(flattening,[],[f30])).
% 3.60/1.02  
% 3.60/1.02  fof(f33,plain,(
% 3.60/1.02    ( ! [X0] : (? [X1] : ((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~sP0(sK6,X0) | ~v3_pre_topc(sK6,X0)) & (sP0(sK6,X0) | v3_pre_topc(sK6,X0)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.60/1.02    introduced(choice_axiom,[])).
% 3.60/1.02  
% 3.60/1.02  fof(f32,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : ((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~sP0(X1,sK5) | ~v3_pre_topc(X1,sK5)) & (sP0(X1,sK5) | v3_pre_topc(X1,sK5)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 3.60/1.02    introduced(choice_axiom,[])).
% 3.60/1.02  
% 3.60/1.02  fof(f34,plain,(
% 3.60/1.02    ((~sP0(sK6,sK5) | ~v3_pre_topc(sK6,sK5)) & (sP0(sK6,sK5) | v3_pre_topc(sK6,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5) & v2_pre_topc(sK5)),
% 3.60/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f33,f32])).
% 3.60/1.02  
% 3.60/1.02  fof(f56,plain,(
% 3.60/1.02    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 3.60/1.02    inference(cnf_transformation,[],[f34])).
% 3.60/1.02  
% 3.60/1.02  fof(f24,plain,(
% 3.60/1.02    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1))) | ~sP0(X1,X0)))),
% 3.60/1.02    inference(nnf_transformation,[],[f16])).
% 3.60/1.02  
% 3.60/1.02  fof(f25,plain,(
% 3.60/1.02    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 3.60/1.02    inference(rectify,[],[f24])).
% 3.60/1.02  
% 3.60/1.02  fof(f28,plain,(
% 3.60/1.02    ! [X5,X1,X0] : (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X5,sK4(X0,X1,X5)) & r1_tarski(sK4(X0,X1,X5),X0) & v3_pre_topc(sK4(X0,X1,X5),X1) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.60/1.02    introduced(choice_axiom,[])).
% 3.60/1.02  
% 3.60/1.02  fof(f27,plain,(
% 3.60/1.02    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X2,sK3(X0,X1)) & r1_tarski(sK3(X0,X1),X0) & v3_pre_topc(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 3.60/1.02    introduced(choice_axiom,[])).
% 3.60/1.02  
% 3.60/1.02  fof(f26,plain,(
% 3.60/1.02    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0))) => ((! [X3] : (~r2_hidden(sK2(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),X0)) & (? [X4] : (r2_hidden(sK2(X0,X1),X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),X0))))),
% 3.60/1.02    introduced(choice_axiom,[])).
% 3.60/1.02  
% 3.60/1.02  fof(f29,plain,(
% 3.60/1.02    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (~r2_hidden(sK2(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),X0)) & ((r2_hidden(sK2(X0,X1),sK3(X0,X1)) & r1_tarski(sK3(X0,X1),X0) & v3_pre_topc(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((r2_hidden(X5,sK4(X0,X1,X5)) & r1_tarski(sK4(X0,X1,X5),X0) & v3_pre_topc(sK4(X0,X1,X5),X1) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 3.60/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).
% 3.60/1.02  
% 3.60/1.02  fof(f46,plain,(
% 3.60/1.02    ( ! [X0,X5,X1] : (r1_tarski(sK4(X0,X1,X5),X0) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f29])).
% 3.60/1.02  
% 3.60/1.02  fof(f44,plain,(
% 3.60/1.02    ( ! [X0,X5,X1] : (m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f29])).
% 3.60/1.02  
% 3.60/1.02  fof(f5,axiom,(
% 3.60/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f12,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(ennf_transformation,[],[f5])).
% 3.60/1.02  
% 3.60/1.02  fof(f13,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(flattening,[],[f12])).
% 3.60/1.02  
% 3.60/1.02  fof(f43,plain,(
% 3.60/1.02    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f13])).
% 3.60/1.02  
% 3.60/1.02  fof(f55,plain,(
% 3.60/1.02    l1_pre_topc(sK5)),
% 3.60/1.02    inference(cnf_transformation,[],[f34])).
% 3.60/1.02  
% 3.60/1.02  fof(f45,plain,(
% 3.60/1.02    ( ! [X0,X5,X1] : (v3_pre_topc(sK4(X0,X1,X5),X1) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f29])).
% 3.60/1.02  
% 3.60/1.02  fof(f47,plain,(
% 3.60/1.02    ( ! [X0,X5,X1] : (r2_hidden(X5,sK4(X0,X1,X5)) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f29])).
% 3.60/1.02  
% 3.60/1.02  fof(f35,plain,(
% 3.60/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f21])).
% 3.60/1.02  
% 3.60/1.02  fof(f57,plain,(
% 3.60/1.02    sP0(sK6,sK5) | v3_pre_topc(sK6,sK5)),
% 3.60/1.02    inference(cnf_transformation,[],[f34])).
% 3.60/1.02  
% 3.60/1.02  fof(f49,plain,(
% 3.60/1.02    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1),X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f29])).
% 3.60/1.02  
% 3.60/1.02  fof(f53,plain,(
% 3.60/1.02    ( ! [X0,X3,X1] : (sP0(X0,X1) | ~r2_hidden(sK2(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1),X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f29])).
% 3.60/1.02  
% 3.60/1.02  fof(f58,plain,(
% 3.60/1.02    ~sP0(sK6,sK5) | ~v3_pre_topc(sK6,sK5)),
% 3.60/1.02    inference(cnf_transformation,[],[f34])).
% 3.60/1.02  
% 3.60/1.02  fof(f2,axiom,(
% 3.60/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f22,plain,(
% 3.60/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.60/1.02    inference(nnf_transformation,[],[f2])).
% 3.60/1.02  
% 3.60/1.02  fof(f23,plain,(
% 3.60/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.60/1.02    inference(flattening,[],[f22])).
% 3.60/1.02  
% 3.60/1.02  fof(f39,plain,(
% 3.60/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.60/1.02    inference(cnf_transformation,[],[f23])).
% 3.60/1.02  
% 3.60/1.02  fof(f59,plain,(
% 3.60/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.60/1.02    inference(equality_resolution,[],[f39])).
% 3.60/1.02  
% 3.60/1.02  fof(f40,plain,(
% 3.60/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f23])).
% 3.60/1.02  
% 3.60/1.02  fof(f51,plain,(
% 3.60/1.02    ( ! [X0,X1] : (sP0(X0,X1) | r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK2(X0,X1),X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f29])).
% 3.60/1.02  
% 3.60/1.02  fof(f52,plain,(
% 3.60/1.02    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(sK2(X0,X1),X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f29])).
% 3.60/1.02  
% 3.60/1.02  fof(f37,plain,(
% 3.60/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f21])).
% 3.60/1.02  
% 3.60/1.02  fof(f4,axiom,(
% 3.60/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f11,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(ennf_transformation,[],[f4])).
% 3.60/1.02  
% 3.60/1.02  fof(f42,plain,(
% 3.60/1.02    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f11])).
% 3.60/1.02  
% 3.60/1.02  fof(f3,axiom,(
% 3.60/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f9,plain,(
% 3.60/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.60/1.02    inference(ennf_transformation,[],[f3])).
% 3.60/1.02  
% 3.60/1.02  fof(f10,plain,(
% 3.60/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.60/1.02    inference(flattening,[],[f9])).
% 3.60/1.02  
% 3.60/1.02  fof(f41,plain,(
% 3.60/1.02    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f10])).
% 3.60/1.02  
% 3.60/1.02  fof(f54,plain,(
% 3.60/1.02    v2_pre_topc(sK5)),
% 3.60/1.02    inference(cnf_transformation,[],[f34])).
% 3.60/1.02  
% 3.60/1.02  fof(f38,plain,(
% 3.60/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.60/1.02    inference(cnf_transformation,[],[f23])).
% 3.60/1.02  
% 3.60/1.02  fof(f60,plain,(
% 3.60/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.60/1.02    inference(equality_resolution,[],[f38])).
% 3.60/1.02  
% 3.60/1.02  cnf(c_1,plain,
% 3.60/1.02      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.60/1.02      inference(cnf_transformation,[],[f36]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2957,plain,
% 3.60/1.02      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 3.60/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_21,negated_conjecture,
% 3.60/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.60/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2941,plain,
% 3.60/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_16,plain,
% 3.60/1.02      ( ~ sP0(X0,X1) | ~ r2_hidden(X2,X0) | r1_tarski(sK4(X0,X1,X2),X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2946,plain,
% 3.60/1.02      ( sP0(X0,X1) != iProver_top
% 3.60/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,X1,X2),X0) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_18,plain,
% 3.60/1.02      ( ~ sP0(X0,X1)
% 3.60/1.02      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ r2_hidden(X2,X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2944,plain,
% 3.60/1.02      ( sP0(X0,X1) != iProver_top
% 3.60/1.02      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.60/1.02      | r2_hidden(X2,X0) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_8,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ v3_pre_topc(X0,X1)
% 3.60/1.02      | ~ r1_tarski(X0,X2)
% 3.60/1.02      | r1_tarski(X0,k1_tops_1(X1,X2))
% 3.60/1.02      | ~ l1_pre_topc(X1) ),
% 3.60/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_22,negated_conjecture,
% 3.60/1.02      ( l1_pre_topc(sK5) ),
% 3.60/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_327,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ v3_pre_topc(X0,X1)
% 3.60/1.02      | ~ r1_tarski(X0,X2)
% 3.60/1.02      | r1_tarski(X0,k1_tops_1(X1,X2))
% 3.60/1.02      | sK5 != X1 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_328,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | ~ v3_pre_topc(X0,sK5)
% 3.60/1.02      | ~ r1_tarski(X0,X1)
% 3.60/1.02      | r1_tarski(X0,k1_tops_1(sK5,X1)) ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_327]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2939,plain,
% 3.60/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | v3_pre_topc(X0,sK5) != iProver_top
% 3.60/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.60/1.02      | r1_tarski(X0,k1_tops_1(sK5,X1)) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3609,plain,
% 3.60/1.02      ( sP0(X0,sK5) != iProver_top
% 3.60/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | v3_pre_topc(sK4(X0,sK5,X2),sK5) != iProver_top
% 3.60/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),X1) != iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) = iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2944,c_2939]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_17,plain,
% 3.60/1.02      ( ~ sP0(X0,X1)
% 3.60/1.02      | v3_pre_topc(sK4(X0,X1,X2),X1)
% 3.60/1.02      | ~ r2_hidden(X2,X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_559,plain,
% 3.60/1.02      ( ~ sP0(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | ~ r2_hidden(X4,X0)
% 3.60/1.02      | ~ r1_tarski(X3,X2)
% 3.60/1.02      | r1_tarski(X3,k1_tops_1(sK5,X2))
% 3.60/1.02      | sK4(X0,X1,X4) != X3
% 3.60/1.02      | sK5 != X1 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_328]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_560,plain,
% 3.60/1.02      ( ~ sP0(X0,sK5)
% 3.60/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | ~ m1_subset_1(sK4(X0,sK5,X2),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | ~ r2_hidden(X2,X0)
% 3.60/1.02      | ~ r1_tarski(sK4(X0,sK5,X2),X1)
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_559]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_576,plain,
% 3.60/1.02      ( ~ sP0(X0,sK5)
% 3.60/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | ~ r2_hidden(X2,X0)
% 3.60/1.02      | ~ r1_tarski(sK4(X0,sK5,X2),X1)
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) ),
% 3.60/1.02      inference(forward_subsumption_resolution,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_560,c_18]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_582,plain,
% 3.60/1.02      ( sP0(X0,sK5) != iProver_top
% 3.60/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),X1) != iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4144,plain,
% 3.60/1.02      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | sP0(X0,sK5) != iProver_top
% 3.60/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),X1) != iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) = iProver_top ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_3609,c_582]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4145,plain,
% 3.60/1.02      ( sP0(X0,sK5) != iProver_top
% 3.60/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),X1) != iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),k1_tops_1(sK5,X1)) = iProver_top ),
% 3.60/1.02      inference(renaming,[status(thm)],[c_4144]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_15,plain,
% 3.60/1.02      ( ~ sP0(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,sK4(X0,X1,X2)) ),
% 3.60/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2947,plain,
% 3.60/1.02      ( sP0(X0,X1) != iProver_top
% 3.60/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.60/1.02      | r2_hidden(X2,sK4(X0,X1,X2)) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2,plain,
% 3.60/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.60/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2956,plain,
% 3.60/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.60/1.02      | r2_hidden(X0,X2) = iProver_top
% 3.60/1.02      | r1_tarski(X1,X2) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3896,plain,
% 3.60/1.02      ( sP0(X0,X1) != iProver_top
% 3.60/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.60/1.02      | r2_hidden(X2,X3) = iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,X1,X2),X3) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2947,c_2956]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_6599,plain,
% 3.60/1.02      ( sP0(X0,sK5) != iProver_top
% 3.60/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.60/1.02      | r2_hidden(X2,k1_tops_1(sK5,X1)) = iProver_top
% 3.60/1.02      | r1_tarski(sK4(X0,sK5,X2),X1) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_4145,c_3896]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_10127,plain,
% 3.60/1.02      ( sP0(X0,sK5) != iProver_top
% 3.60/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | r2_hidden(X1,X0) != iProver_top
% 3.60/1.02      | r2_hidden(X1,k1_tops_1(sK5,X0)) = iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2946,c_6599]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_10289,plain,
% 3.60/1.02      ( sP0(sK6,sK5) != iProver_top
% 3.60/1.02      | r2_hidden(X0,k1_tops_1(sK5,sK6)) = iProver_top
% 3.60/1.02      | r2_hidden(X0,sK6) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2941,c_10127]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_20,negated_conjecture,
% 3.60/1.02      ( sP0(sK6,sK5) | v3_pre_topc(sK6,sK5) ),
% 3.60/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_27,plain,
% 3.60/1.02      ( sP0(sK6,sK5) = iProver_top | v3_pre_topc(sK6,sK5) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_13,plain,
% 3.60/1.02      ( sP0(X0,X1)
% 3.60/1.02      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2949,plain,
% 3.60/1.02      ( sP0(X0,X1) = iProver_top
% 3.60/1.02      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_9,plain,
% 3.60/1.02      ( sP0(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ v3_pre_topc(X2,X1)
% 3.60/1.02      | ~ r2_hidden(sK2(X0,X1),X2)
% 3.60/1.02      | ~ r2_hidden(sK2(X0,X1),X0)
% 3.60/1.02      | ~ r1_tarski(X2,X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2953,plain,
% 3.60/1.02      ( sP0(X0,X1) = iProver_top
% 3.60/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.60/1.02      | v3_pre_topc(X2,X1) != iProver_top
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X0) != iProver_top
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X2) != iProver_top
% 3.60/1.02      | r1_tarski(X2,X0) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3063,plain,
% 3.60/1.02      ( sP0(X0,X1) = iProver_top
% 3.60/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.60/1.02      | v3_pre_topc(X2,X1) != iProver_top
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X2) != iProver_top
% 3.60/1.02      | r1_tarski(X2,X0) != iProver_top ),
% 3.60/1.02      inference(forward_subsumption_resolution,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_2953,c_2956]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5477,plain,
% 3.60/1.02      ( sP0(X0,sK5) = iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,sK5) != iProver_top
% 3.60/1.02      | r2_hidden(sK2(X0,sK5),sK6) != iProver_top
% 3.60/1.02      | r1_tarski(sK6,X0) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2941,c_3063]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5666,plain,
% 3.60/1.02      ( sP0(sK6,sK5) = iProver_top
% 3.60/1.02      | m1_subset_1(sK3(sK6,sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,sK5) != iProver_top
% 3.60/1.02      | r1_tarski(sK6,sK6) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2949,c_5477]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_26,plain,
% 3.60/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_19,negated_conjecture,
% 3.60/1.02      ( ~ sP0(sK6,sK5) | ~ v3_pre_topc(sK6,sK5) ),
% 3.60/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_28,plain,
% 3.60/1.02      ( sP0(sK6,sK5) != iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,sK5) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4,plain,
% 3.60/1.02      ( r1_tarski(X0,X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4237,plain,
% 3.60/1.02      ( r1_tarski(sK6,sK6) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4242,plain,
% 3.60/1.02      ( r1_tarski(sK6,sK6) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_4237]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4746,plain,
% 3.60/1.02      ( sP0(X0,sK5)
% 3.60/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | ~ v3_pre_topc(sK6,sK5)
% 3.60/1.02      | ~ r2_hidden(sK2(X0,sK5),X0)
% 3.60/1.02      | ~ r2_hidden(sK2(X0,sK5),sK6)
% 3.60/1.02      | ~ r1_tarski(sK6,X0) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4766,plain,
% 3.60/1.02      ( sP0(sK6,sK5)
% 3.60/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | ~ v3_pre_topc(sK6,sK5)
% 3.60/1.02      | ~ r2_hidden(sK2(sK6,sK5),sK6)
% 3.60/1.02      | ~ r1_tarski(sK6,sK6) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_4746]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4767,plain,
% 3.60/1.02      ( sP0(sK6,sK5) = iProver_top
% 3.60/1.02      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,sK5) != iProver_top
% 3.60/1.02      | r2_hidden(sK2(sK6,sK5),sK6) != iProver_top
% 3.60/1.02      | r1_tarski(sK6,sK6) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_4766]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5216,plain,
% 3.60/1.02      ( sP0(sK6,sK5)
% 3.60/1.02      | m1_subset_1(sK3(sK6,sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | r2_hidden(sK2(sK6,sK5),sK6) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5223,plain,
% 3.60/1.02      ( sP0(sK6,sK5) = iProver_top
% 3.60/1.02      | m1_subset_1(sK3(sK6,sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.60/1.02      | r2_hidden(sK2(sK6,sK5),sK6) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_5216]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5950,plain,
% 3.60/1.02      ( v3_pre_topc(sK6,sK5) != iProver_top
% 3.60/1.02      | m1_subset_1(sK3(sK6,sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_5666,c_26,c_28,c_4242,c_4767,c_5223]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5951,plain,
% 3.60/1.02      ( m1_subset_1(sK3(sK6,sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,sK5) != iProver_top ),
% 3.60/1.02      inference(renaming,[status(thm)],[c_5950]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3210,plain,
% 3.60/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,sK5) != iProver_top
% 3.60/1.02      | r1_tarski(sK6,X0) != iProver_top
% 3.60/1.02      | r1_tarski(sK6,k1_tops_1(sK5,X0)) = iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2941,c_2939]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5957,plain,
% 3.60/1.02      ( v3_pre_topc(sK6,sK5) != iProver_top
% 3.60/1.02      | r1_tarski(sK6,sK3(sK6,sK5)) != iProver_top
% 3.60/1.02      | r1_tarski(sK6,k1_tops_1(sK5,sK3(sK6,sK5))) = iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_5951,c_3210]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3,plain,
% 3.60/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.60/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2955,plain,
% 3.60/1.02      ( X0 = X1
% 3.60/1.02      | r1_tarski(X1,X0) != iProver_top
% 3.60/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_6270,plain,
% 3.60/1.02      ( k1_tops_1(sK5,sK3(sK6,sK5)) = sK6
% 3.60/1.02      | v3_pre_topc(sK6,sK5) != iProver_top
% 3.60/1.02      | r1_tarski(k1_tops_1(sK5,sK3(sK6,sK5)),sK6) != iProver_top
% 3.60/1.02      | r1_tarski(sK6,sK3(sK6,sK5)) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_5957,c_2955]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_11,plain,
% 3.60/1.02      ( sP0(X0,X1)
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X0)
% 3.60/1.02      | r1_tarski(sK3(X0,X1),X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2951,plain,
% 3.60/1.02      ( sP0(X0,X1) = iProver_top
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 3.60/1.02      | r1_tarski(sK3(X0,X1),X0) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5667,plain,
% 3.60/1.02      ( sP0(sK6,sK5) = iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,sK5) != iProver_top
% 3.60/1.02      | r1_tarski(sK3(sK6,sK5),sK6) = iProver_top
% 3.60/1.02      | r1_tarski(sK6,sK6) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2951,c_5477]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5822,plain,
% 3.60/1.02      ( r1_tarski(sK3(sK6,sK5),sK6) = iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,sK5) != iProver_top ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_5667,c_28,c_4242]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5823,plain,
% 3.60/1.02      ( v3_pre_topc(sK6,sK5) != iProver_top
% 3.60/1.02      | r1_tarski(sK3(sK6,sK5),sK6) = iProver_top ),
% 3.60/1.02      inference(renaming,[status(thm)],[c_5822]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_10,plain,
% 3.60/1.02      ( sP0(X0,X1)
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X0)
% 3.60/1.02      | r2_hidden(sK2(X0,X1),sK3(X0,X1)) ),
% 3.60/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2952,plain,
% 3.60/1.02      ( sP0(X0,X1) = iProver_top
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 3.60/1.02      | r2_hidden(sK2(X0,X1),sK3(X0,X1)) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4472,plain,
% 3.60/1.02      ( sP0(X0,X1) = iProver_top
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 3.60/1.02      | r2_hidden(sK2(X0,X1),X2) = iProver_top
% 3.60/1.02      | r1_tarski(sK3(X0,X1),X2) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2952,c_2956]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_8202,plain,
% 3.60/1.02      ( sP0(sK6,sK5) = iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,sK5) != iProver_top
% 3.60/1.02      | r2_hidden(sK2(sK6,sK5),sK6) = iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_5823,c_4472]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_8721,plain,
% 3.60/1.02      ( v3_pre_topc(sK6,sK5) != iProver_top ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_6270,c_26,c_28,c_4242,c_4767,c_8202]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_10340,plain,
% 3.60/1.02      ( r2_hidden(X0,k1_tops_1(sK5,sK6)) = iProver_top
% 3.60/1.02      | r2_hidden(X0,sK6) != iProver_top ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_10289,c_26,c_27,c_28,c_4242,c_4767,c_8202]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_0,plain,
% 3.60/1.02      ( ~ r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.60/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2958,plain,
% 3.60/1.02      ( r2_hidden(sK1(X0,X1),X1) != iProver_top
% 3.60/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_10348,plain,
% 3.60/1.02      ( r2_hidden(sK1(X0,k1_tops_1(sK5,sK6)),sK6) != iProver_top
% 3.60/1.02      | r1_tarski(X0,k1_tops_1(sK5,sK6)) = iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_10340,c_2958]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_10533,plain,
% 3.60/1.02      ( r1_tarski(sK6,k1_tops_1(sK5,sK6)) = iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2957,c_10348]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2427,plain,
% 3.60/1.02      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.60/1.02      theory(equality) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3148,plain,
% 3.60/1.02      ( v3_pre_topc(X0,X1)
% 3.60/1.02      | ~ v3_pre_topc(k1_tops_1(sK5,sK6),sK5)
% 3.60/1.02      | X0 != k1_tops_1(sK5,sK6)
% 3.60/1.02      | X1 != sK5 ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_2427]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3410,plain,
% 3.60/1.02      ( ~ v3_pre_topc(k1_tops_1(sK5,sK6),sK5)
% 3.60/1.02      | v3_pre_topc(sK6,X0)
% 3.60/1.02      | X0 != sK5
% 3.60/1.02      | sK6 != k1_tops_1(sK5,sK6) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_3148]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3412,plain,
% 3.60/1.02      ( X0 != sK5
% 3.60/1.02      | sK6 != k1_tops_1(sK5,sK6)
% 3.60/1.02      | v3_pre_topc(k1_tops_1(sK5,sK6),sK5) != iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,X0) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_3410]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3414,plain,
% 3.60/1.02      ( sK5 != sK5
% 3.60/1.02      | sK6 != k1_tops_1(sK5,sK6)
% 3.60/1.02      | v3_pre_topc(k1_tops_1(sK5,sK6),sK5) != iProver_top
% 3.60/1.02      | v3_pre_topc(sK6,sK5) = iProver_top ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_3412]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3214,plain,
% 3.60/1.02      ( ~ r1_tarski(X0,k1_tops_1(sK5,sK6))
% 3.60/1.02      | ~ r1_tarski(k1_tops_1(sK5,sK6),X0)
% 3.60/1.02      | X0 = k1_tops_1(sK5,sK6) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3344,plain,
% 3.60/1.02      ( ~ r1_tarski(k1_tops_1(sK5,sK6),sK6)
% 3.60/1.02      | ~ r1_tarski(sK6,k1_tops_1(sK5,sK6))
% 3.60/1.02      | sK6 = k1_tops_1(sK5,sK6) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_3214]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3347,plain,
% 3.60/1.02      ( sK6 = k1_tops_1(sK5,sK6)
% 3.60/1.02      | r1_tarski(k1_tops_1(sK5,sK6),sK6) != iProver_top
% 3.60/1.02      | r1_tarski(sK6,k1_tops_1(sK5,sK6)) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_3344]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_7,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.60/1.02      | ~ l1_pre_topc(X1) ),
% 3.60/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_348,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.60/1.02      | sK5 != X1 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_349,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | r1_tarski(k1_tops_1(sK5,X0),X0) ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_348]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3118,plain,
% 3.60/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | r1_tarski(k1_tops_1(sK5,sK6),sK6) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_349]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3119,plain,
% 3.60/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | r1_tarski(k1_tops_1(sK5,sK6),sK6) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_3118]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_6,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | v3_pre_topc(k1_tops_1(X1,X0),X1)
% 3.60/1.02      | ~ v2_pre_topc(X1)
% 3.60/1.02      | ~ l1_pre_topc(X1) ),
% 3.60/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_23,negated_conjecture,
% 3.60/1.02      ( v2_pre_topc(sK5) ),
% 3.60/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_306,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | v3_pre_topc(k1_tops_1(X1,X0),X1)
% 3.60/1.02      | ~ l1_pre_topc(X1)
% 3.60/1.02      | sK5 != X1 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_307,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | v3_pre_topc(k1_tops_1(sK5,X0),sK5)
% 3.60/1.02      | ~ l1_pre_topc(sK5) ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_306]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_311,plain,
% 3.60/1.02      ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_307,c_22]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_312,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | v3_pre_topc(k1_tops_1(sK5,X0),sK5) ),
% 3.60/1.02      inference(renaming,[status(thm)],[c_311]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3115,plain,
% 3.60/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.60/1.02      | v3_pre_topc(k1_tops_1(sK5,sK6),sK5) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_312]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3116,plain,
% 3.60/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.60/1.02      | v3_pre_topc(k1_tops_1(sK5,sK6),sK5) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_3115]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_71,plain,
% 3.60/1.02      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5,plain,
% 3.60/1.02      ( r1_tarski(X0,X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_67,plain,
% 3.60/1.02      ( r1_tarski(sK5,sK5) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(contradiction,plain,
% 3.60/1.02      ( $false ),
% 3.60/1.02      inference(minisat,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_10533,c_8721,c_3414,c_3347,c_3119,c_3116,c_71,c_67,
% 3.60/1.02                 c_26]) ).
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/1.02  
% 3.60/1.02  ------                               Statistics
% 3.60/1.02  
% 3.60/1.02  ------ General
% 3.60/1.02  
% 3.60/1.02  abstr_ref_over_cycles:                  0
% 3.60/1.02  abstr_ref_under_cycles:                 0
% 3.60/1.02  gc_basic_clause_elim:                   0
% 3.60/1.02  forced_gc_time:                         0
% 3.60/1.02  parsing_time:                           0.008
% 3.60/1.02  unif_index_cands_time:                  0.
% 3.60/1.02  unif_index_add_time:                    0.
% 3.60/1.02  orderings_time:                         0.
% 3.60/1.02  out_proof_time:                         0.009
% 3.60/1.02  total_time:                             0.285
% 3.60/1.02  num_of_symbols:                         47
% 3.60/1.02  num_of_terms:                           5625
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing
% 3.60/1.02  
% 3.60/1.02  num_of_splits:                          0
% 3.60/1.02  num_of_split_atoms:                     0
% 3.60/1.02  num_of_reused_defs:                     0
% 3.60/1.02  num_eq_ax_congr_red:                    31
% 3.60/1.02  num_of_sem_filtered_clauses:            1
% 3.60/1.02  num_of_subtypes:                        0
% 3.60/1.02  monotx_restored_types:                  0
% 3.60/1.02  sat_num_of_epr_types:                   0
% 3.60/1.02  sat_num_of_non_cyclic_types:            0
% 3.60/1.02  sat_guarded_non_collapsed_types:        0
% 3.60/1.02  num_pure_diseq_elim:                    0
% 3.60/1.02  simp_replaced_by:                       0
% 3.60/1.02  res_preprocessed:                       107
% 3.60/1.02  prep_upred:                             0
% 3.60/1.02  prep_unflattend:                        91
% 3.60/1.02  smt_new_axioms:                         0
% 3.60/1.02  pred_elim_cands:                        5
% 3.60/1.02  pred_elim:                              2
% 3.60/1.02  pred_elim_cl:                           2
% 3.60/1.02  pred_elim_cycles:                       6
% 3.60/1.02  merged_defs:                            8
% 3.60/1.02  merged_defs_ncl:                        0
% 3.60/1.02  bin_hyper_res:                          8
% 3.60/1.02  prep_cycles:                            4
% 3.60/1.02  pred_elim_time:                         0.038
% 3.60/1.02  splitting_time:                         0.
% 3.60/1.02  sem_filter_time:                        0.
% 3.60/1.02  monotx_time:                            0.001
% 3.60/1.02  subtype_inf_time:                       0.
% 3.60/1.02  
% 3.60/1.02  ------ Problem properties
% 3.60/1.02  
% 3.60/1.02  clauses:                                21
% 3.60/1.02  conjectures:                            3
% 3.60/1.02  epr:                                    5
% 3.60/1.02  horn:                                   15
% 3.60/1.02  ground:                                 3
% 3.60/1.02  unary:                                  2
% 3.60/1.02  binary:                                 6
% 3.60/1.02  lits:                                   61
% 3.60/1.02  lits_eq:                                1
% 3.60/1.02  fd_pure:                                0
% 3.60/1.02  fd_pseudo:                              0
% 3.60/1.02  fd_cond:                                0
% 3.60/1.02  fd_pseudo_cond:                         1
% 3.60/1.02  ac_symbols:                             0
% 3.60/1.02  
% 3.60/1.02  ------ Propositional Solver
% 3.60/1.02  
% 3.60/1.02  prop_solver_calls:                      30
% 3.60/1.02  prop_fast_solver_calls:                 1733
% 3.60/1.02  smt_solver_calls:                       0
% 3.60/1.02  smt_fast_solver_calls:                  0
% 3.60/1.02  prop_num_of_clauses:                    2811
% 3.60/1.02  prop_preprocess_simplified:             7706
% 3.60/1.02  prop_fo_subsumed:                       87
% 3.60/1.02  prop_solver_time:                       0.
% 3.60/1.02  smt_solver_time:                        0.
% 3.60/1.02  smt_fast_solver_time:                   0.
% 3.60/1.02  prop_fast_solver_time:                  0.
% 3.60/1.02  prop_unsat_core_time:                   0.
% 3.60/1.02  
% 3.60/1.02  ------ QBF
% 3.60/1.02  
% 3.60/1.02  qbf_q_res:                              0
% 3.60/1.02  qbf_num_tautologies:                    0
% 3.60/1.02  qbf_prep_cycles:                        0
% 3.60/1.02  
% 3.60/1.02  ------ BMC1
% 3.60/1.02  
% 3.60/1.02  bmc1_current_bound:                     -1
% 3.60/1.02  bmc1_last_solved_bound:                 -1
% 3.60/1.02  bmc1_unsat_core_size:                   -1
% 3.60/1.02  bmc1_unsat_core_parents_size:           -1
% 3.60/1.02  bmc1_merge_next_fun:                    0
% 3.60/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.60/1.02  
% 3.60/1.02  ------ Instantiation
% 3.60/1.02  
% 3.60/1.02  inst_num_of_clauses:                    701
% 3.60/1.02  inst_num_in_passive:                    233
% 3.60/1.02  inst_num_in_active:                     322
% 3.60/1.02  inst_num_in_unprocessed:                146
% 3.60/1.02  inst_num_of_loops:                      470
% 3.60/1.02  inst_num_of_learning_restarts:          0
% 3.60/1.02  inst_num_moves_active_passive:          143
% 3.60/1.02  inst_lit_activity:                      0
% 3.60/1.02  inst_lit_activity_moves:                0
% 3.60/1.02  inst_num_tautologies:                   0
% 3.60/1.02  inst_num_prop_implied:                  0
% 3.60/1.02  inst_num_existing_simplified:           0
% 3.60/1.02  inst_num_eq_res_simplified:             0
% 3.60/1.02  inst_num_child_elim:                    0
% 3.60/1.02  inst_num_of_dismatching_blockings:      146
% 3.60/1.02  inst_num_of_non_proper_insts:           804
% 3.60/1.02  inst_num_of_duplicates:                 0
% 3.60/1.02  inst_inst_num_from_inst_to_res:         0
% 3.60/1.02  inst_dismatching_checking_time:         0.
% 3.60/1.02  
% 3.60/1.02  ------ Resolution
% 3.60/1.02  
% 3.60/1.02  res_num_of_clauses:                     0
% 3.60/1.02  res_num_in_passive:                     0
% 3.60/1.02  res_num_in_active:                      0
% 3.60/1.02  res_num_of_loops:                       111
% 3.60/1.02  res_forward_subset_subsumed:            137
% 3.60/1.02  res_backward_subset_subsumed:           0
% 3.60/1.02  res_forward_subsumed:                   20
% 3.60/1.02  res_backward_subsumed:                  0
% 3.60/1.02  res_forward_subsumption_resolution:     13
% 3.60/1.02  res_backward_subsumption_resolution:    0
% 3.60/1.02  res_clause_to_clause_subsumption:       1756
% 3.60/1.02  res_orphan_elimination:                 0
% 3.60/1.02  res_tautology_del:                      141
% 3.60/1.02  res_num_eq_res_simplified:              0
% 3.60/1.02  res_num_sel_changes:                    0
% 3.60/1.02  res_moves_from_active_to_pass:          0
% 3.60/1.02  
% 3.60/1.02  ------ Superposition
% 3.60/1.02  
% 3.60/1.02  sup_time_total:                         0.
% 3.60/1.02  sup_time_generating:                    0.
% 3.60/1.02  sup_time_sim_full:                      0.
% 3.60/1.02  sup_time_sim_immed:                     0.
% 3.60/1.02  
% 3.60/1.02  sup_num_of_clauses:                     186
% 3.60/1.02  sup_num_in_active:                      83
% 3.60/1.02  sup_num_in_passive:                     103
% 3.60/1.02  sup_num_of_loops:                       92
% 3.60/1.02  sup_fw_superposition:                   169
% 3.60/1.02  sup_bw_superposition:                   120
% 3.60/1.02  sup_immediate_simplified:               45
% 3.60/1.02  sup_given_eliminated:                   0
% 3.60/1.02  comparisons_done:                       0
% 3.60/1.02  comparisons_avoided:                    2
% 3.60/1.02  
% 3.60/1.02  ------ Simplifications
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  sim_fw_subset_subsumed:                 24
% 3.60/1.02  sim_bw_subset_subsumed:                 28
% 3.60/1.02  sim_fw_subsumed:                        21
% 3.60/1.02  sim_bw_subsumed:                        4
% 3.60/1.02  sim_fw_subsumption_res:                 4
% 3.60/1.02  sim_bw_subsumption_res:                 0
% 3.60/1.02  sim_tautology_del:                      11
% 3.60/1.02  sim_eq_tautology_del:                   6
% 3.60/1.02  sim_eq_res_simp:                        0
% 3.60/1.02  sim_fw_demodulated:                     1
% 3.60/1.02  sim_bw_demodulated:                     0
% 3.60/1.02  sim_light_normalised:                   0
% 3.60/1.02  sim_joinable_taut:                      0
% 3.60/1.02  sim_joinable_simp:                      0
% 3.60/1.02  sim_ac_normalised:                      0
% 3.60/1.02  sim_smt_subsumption:                    0
% 3.60/1.02  
%------------------------------------------------------------------------------
