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
% DateTime   : Thu Dec  3 12:14:03 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 812 expanded)
%              Number of clauses        :  118 ( 202 expanded)
%              Number of leaves         :   15 ( 210 expanded)
%              Depth                    :   25
%              Number of atoms          :  782 (5685 expanded)
%              Number of equality atoms :  171 ( 291 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
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
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
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
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK2(X0,X1,X2))
        & r1_tarski(sK2(X0,X1,X2),X2)
        & v3_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK2(X0,X1,X2))
                & r1_tarski(sK2(X0,X1,X2),X2)
                & v3_pre_topc(sK2(X0,X1,X2),X0)
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
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

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ sP0(X1,X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( sP0(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ sP0(X1,X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( sP0(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ sP0(sK7,X0)
          | ~ v3_pre_topc(sK7,X0) )
        & ( sP0(sK7,X0)
          | v3_pre_topc(sK7,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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
          ( ( ~ sP0(X1,sK6)
            | ~ v3_pre_topc(X1,sK6) )
          & ( sP0(X1,sK6)
            | v3_pre_topc(X1,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ sP0(sK7,sK6)
      | ~ v3_pre_topc(sK7,sK6) )
    & ( sP0(sK7,sK6)
      | v3_pre_topc(sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f35,f37,f36])).

fof(f62,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( r2_hidden(X5,X7)
          & r1_tarski(X7,X0)
          & v3_pre_topc(X7,X1)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(X5,sK5(X0,X1,X5))
        & r1_tarski(sK5(X0,X1,X5),X0)
        & v3_pre_topc(sK5(X0,X1,X5),X1)
        & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X2,X4)
          & r1_tarski(X4,X0)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(X2,sK4(X0,X1))
        & r1_tarski(sK4(X0,X1),X0)
        & v3_pre_topc(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
              ( ~ r2_hidden(sK3(X0,X1),X3)
              | ~ r1_tarski(X3,X0)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( ? [X4] :
              ( r2_hidden(sK3(X0,X1),X4)
              & r1_tarski(X4,X0)
              & v3_pre_topc(X4,X1)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( ~ r2_hidden(sK3(X0,X1),X3)
                | ~ r1_tarski(X3,X0)
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK3(X0,X1),X0) )
          & ( ( r2_hidden(sK3(X0,X1),sK4(X0,X1))
              & r1_tarski(sK4(X0,X1),X0)
              & v3_pre_topc(sK4(X0,X1),X1)
              & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK3(X0,X1),X0) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X0)
              | ! [X6] :
                  ( ~ r2_hidden(X5,X6)
                  | ~ r1_tarski(X6,X0)
                  | ~ v3_pre_topc(X6,X1)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
            & ( ( r2_hidden(X5,sK5(X0,X1,X5))
                & r1_tarski(sK5(X0,X1,X5),X0)
                & v3_pre_topc(sK5(X0,X1,X5),X1)
                & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X5,X0) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK3(X0,X1),sK4(X0,X1))
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X3)
      | ~ r1_tarski(X3,X0)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,
    ( ~ sP0(sK7,sK6)
    | ~ v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v3_pre_topc(sK4(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_tarski(sK4(X0,X1),X0)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK2(X0,X1,X2))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( v3_pre_topc(sK5(X0,X1,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r1_tarski(sK5(X0,X1,X5),X0)
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK5(X0,X1,X5))
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,
    ( sP0(sK7,sK6)
    | v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(X0,sK6)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k1_tops_1(sK6,X1))
    | ~ r1_tarski(X0,X1)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_445,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X2,k1_tops_1(sK6,X1))
    | ~ r2_hidden(X2,X0)
    | ~ v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_26])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(X0,sK6)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k1_tops_1(sK6,X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_445])).

cnf(c_7594,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK5(sK7,X1,sK1(sK7,k1_tops_1(sK6,sK7))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(sK5(sK7,X1,sK1(sK7,k1_tops_1(sK6,sK7))),sK6)
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK5(sK7,X1,sK1(sK7,k1_tops_1(sK6,sK7))))
    | r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),k1_tops_1(sK6,X0))
    | ~ r1_tarski(sK5(sK7,X1,sK1(sK7,k1_tops_1(sK6,sK7))),X0) ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_10415,plain,
    ( ~ m1_subset_1(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),sK6)
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))))
    | r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),k1_tops_1(sK6,sK7))
    | ~ r1_tarski(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),sK7) ),
    inference(instantiation,[status(thm)],[c_7594])).

cnf(c_10417,plain,
    ( ~ m1_subset_1(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),sK6)
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))))
    | r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),k1_tops_1(sK6,sK7))
    | ~ r1_tarski(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),sK7) ),
    inference(instantiation,[status(thm)],[c_10415])).

cnf(c_14,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK3(X0,X1),X0)
    | r2_hidden(sK3(X0,X1),sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3427,plain,
    ( sP0(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top
    | r2_hidden(sK3(X0,X1),sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3416,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3424,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(sK3(X0,X1),X2)
    | ~ r2_hidden(sK3(X0,X1),X0)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3428,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_pre_topc(X2,X1) != iProver_top
    | r2_hidden(sK3(X0,X1),X0) != iProver_top
    | r2_hidden(sK3(X0,X1),X2) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3431,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3564,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_pre_topc(X2,X1) != iProver_top
    | r2_hidden(sK3(X0,X1),X2) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3428,c_3431])).

cnf(c_5952,plain,
    ( sP0(X0,sK6) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(sK3(X0,sK6),sK7) != iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3416,c_3564])).

cnf(c_6312,plain,
    ( sP0(sK7,sK6) = iProver_top
    | m1_subset_1(sK4(sK7,sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3424,c_5952])).

cnf(c_23,negated_conjecture,
    ( ~ sP0(sK7,sK6)
    | ~ v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,plain,
    ( sP0(sK7,sK6) != iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5845,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5848,plain,
    ( r1_tarski(sK7,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5845])).

cnf(c_7318,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | m1_subset_1(sK4(sK7,sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6312,c_32,c_5848])).

cnf(c_7319,plain,
    ( m1_subset_1(sK4(sK7,sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_7318])).

cnf(c_3411,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v3_pre_topc(X0,sK6) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_tops_1(sK6,X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_7327,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v3_pre_topc(sK4(sK7,sK6),sK6) != iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(X1,sK4(sK7,sK6)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK6,X0)) = iProver_top
    | r1_tarski(sK4(sK7,sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7319,c_3411])).

cnf(c_16,plain,
    ( sP0(X0,X1)
    | v3_pre_topc(sK4(X0,X1),X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3425,plain,
    ( sP0(X0,X1) = iProver_top
    | v3_pre_topc(sK4(X0,X1),X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6314,plain,
    ( sP0(sK7,sK6) = iProver_top
    | v3_pre_topc(sK4(sK7,sK6),sK6) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3425,c_5952])).

cnf(c_6665,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | v3_pre_topc(sK4(sK7,sK6),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6314,c_32,c_5848])).

cnf(c_6666,plain,
    ( v3_pre_topc(sK4(sK7,sK6),sK6) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_6665])).

cnf(c_7767,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(X1,sK4(sK7,sK6)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK6,X0)) = iProver_top
    | r1_tarski(sK4(sK7,sK6),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7327,c_6666])).

cnf(c_7780,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(X0,sK4(sK7,sK6)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK6,sK7)) = iProver_top
    | r1_tarski(sK4(sK7,sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3416,c_7767])).

cnf(c_15,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(sK4(X0,X1),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3426,plain,
    ( sP0(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top
    | r1_tarski(sK4(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6313,plain,
    ( sP0(sK7,sK6) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top
    | r1_tarski(sK4(sK7,sK6),sK7) = iProver_top
    | r1_tarski(sK7,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3426,c_5952])).

cnf(c_6656,plain,
    ( r1_tarski(sK4(sK7,sK6),sK7) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6313,c_32,c_5848])).

cnf(c_6657,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | r1_tarski(sK4(sK7,sK6),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_6656])).

cnf(c_7867,plain,
    ( r2_hidden(X0,k1_tops_1(sK6,sK7)) = iProver_top
    | r2_hidden(X0,sK4(sK7,sK6)) != iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7780,c_6657])).

cnf(c_7868,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(X0,sK4(sK7,sK6)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK6,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7867])).

cnf(c_7880,plain,
    ( sP0(sK7,sK6) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(sK3(sK7,sK6),k1_tops_1(sK6,sK7)) = iProver_top
    | r2_hidden(sK3(sK7,sK6),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3427,c_7868])).

cnf(c_30,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4549,plain,
    ( sP0(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(X0,sK6)
    | ~ r2_hidden(sK3(sK7,sK6),X0)
    | ~ r2_hidden(sK3(sK7,sK6),sK7)
    | ~ r1_tarski(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5699,plain,
    ( sP0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_pre_topc(sK7,sK6)
    | ~ r2_hidden(sK3(sK7,sK6),sK7)
    | ~ r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_4549])).

cnf(c_5700,plain,
    ( sP0(sK7,sK6) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(sK3(sK7,sK6),sK7) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5699])).

cnf(c_8781,plain,
    ( r2_hidden(sK3(sK7,sK6),k1_tops_1(sK6,sK7)) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7880,c_30,c_32,c_5700,c_5848])).

cnf(c_8782,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(sK3(sK7,sK6),k1_tops_1(sK6,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8781])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | r1_tarski(sK2(X1,X2,X0),X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | r1_tarski(sK2(X1,X2,X0),X0)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,k1_tops_1(sK6,X0))
    | r1_tarski(sK2(sK6,X1,X0),X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_403,plain,
    ( r1_tarski(sK2(sK6,X1,X0),X0)
    | ~ r2_hidden(X1,k1_tops_1(sK6,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_26])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,k1_tops_1(sK6,X0))
    | r1_tarski(sK2(sK6,X1,X0),X0) ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_3413,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK6,X0)) != iProver_top
    | r1_tarski(sK2(sK6,X1,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,sK2(X1,X2,X0))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,sK2(X1,X2,X0))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X1,sK2(sK6,X1,X0))
    | ~ r2_hidden(X1,k1_tops_1(sK6,X0))
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_424,plain,
    ( ~ r2_hidden(X1,k1_tops_1(sK6,X0))
    | r2_hidden(X1,sK2(sK6,X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_26])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X1,sK2(sK6,X1,X0))
    | ~ r2_hidden(X1,k1_tops_1(sK6,X0)) ),
    inference(renaming,[status(thm)],[c_424])).

cnf(c_3412,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X1,sK2(sK6,X1,X0)) = iProver_top
    | r2_hidden(X1,k1_tops_1(sK6,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_4371,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k1_tops_1(sK6,X0)) != iProver_top
    | r1_tarski(sK2(sK6,X1,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3412,c_3431])).

cnf(c_4640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k1_tops_1(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3413,c_4371])).

cnf(c_4655,plain,
    ( r2_hidden(X0,k1_tops_1(sK6,sK7)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3416,c_4640])).

cnf(c_8788,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(sK3(sK7,sK6),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_8782,c_4655])).

cnf(c_8859,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8788,c_30,c_32,c_5700,c_5848])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3432,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK6,X0)) = iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3416,c_3411])).

cnf(c_4128,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK6,sK7)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3416,c_3736])).

cnf(c_3429,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4161,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK6,sK7)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4128,c_3429])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3433,plain,
    ( r2_hidden(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4165,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | r2_hidden(sK1(X0,k1_tops_1(sK6,sK7)),sK7) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4161,c_3433])).

cnf(c_6784,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top
    | r1_tarski(sK7,k1_tops_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3432,c_4165])).

cnf(c_6803,plain,
    ( ~ v3_pre_topc(sK7,sK6)
    | r1_tarski(sK7,k1_tops_1(sK6,sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6784])).

cnf(c_2828,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3677,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k1_tops_1(sK6,sK7),sK6)
    | X0 != k1_tops_1(sK6,sK7)
    | X1 != sK6 ),
    inference(instantiation,[status(thm)],[c_2828])).

cnf(c_4274,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK6,sK7),sK6)
    | v3_pre_topc(sK7,X0)
    | X0 != sK6
    | sK7 != k1_tops_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_3677])).

cnf(c_4276,plain,
    ( X0 != sK6
    | sK7 != k1_tops_1(sK6,sK7)
    | v3_pre_topc(k1_tops_1(sK6,sK7),sK6) != iProver_top
    | v3_pre_topc(sK7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4274])).

cnf(c_4278,plain,
    ( sK6 != sK6
    | sK7 != k1_tops_1(sK6,sK7)
    | v3_pre_topc(k1_tops_1(sK6,sK7),sK6) != iProver_top
    | v3_pre_topc(sK7,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4276])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3827,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK6,sK7))
    | ~ r1_tarski(k1_tops_1(sK6,sK7),X0)
    | X0 = k1_tops_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4213,plain,
    ( ~ r1_tarski(k1_tops_1(sK6,sK7),sK7)
    | ~ r1_tarski(sK7,k1_tops_1(sK6,sK7))
    | sK7 = k1_tops_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_3827])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1)
    | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4092,plain,
    ( ~ sP0(sK7,X0)
    | m1_subset_1(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_4109,plain,
    ( ~ sP0(sK7,sK6)
    | m1_subset_1(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_4092])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1)
    | v3_pre_topc(sK5(X0,X1,X2),X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4093,plain,
    ( ~ sP0(sK7,X0)
    | v3_pre_topc(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),X0)
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4105,plain,
    ( ~ sP0(sK7,sK6)
    | v3_pre_topc(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),sK6)
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_4093])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r1_tarski(sK5(X0,X1,X2),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4094,plain,
    ( ~ sP0(sK7,X0)
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7)
    | r1_tarski(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),sK7) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4101,plain,
    ( ~ sP0(sK7,sK6)
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7)
    | r1_tarski(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),sK7) ),
    inference(instantiation,[status(thm)],[c_4094])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4095,plain,
    ( ~ sP0(sK7,X0)
    | r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))))
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4097,plain,
    ( ~ sP0(sK7,sK6)
    | r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))))
    | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_4095])).

cnf(c_3850,plain,
    ( r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7)
    | r1_tarski(sK7,k1_tops_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3851,plain,
    ( ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),k1_tops_1(sK6,sK7))
    | r1_tarski(sK7,k1_tops_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_tarski(k1_tops_1(sK6,X0),X0) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_3627,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_tarski(k1_tops_1(sK6,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(k1_tops_1(X1,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(k1_tops_1(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_27])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v3_pre_topc(k1_tops_1(sK6,X0),sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_475,plain,
    ( v3_pre_topc(k1_tops_1(sK6,X0),sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_26])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v3_pre_topc(k1_tops_1(sK6,X0),sK6) ),
    inference(renaming,[status(thm)],[c_475])).

cnf(c_3624,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | v3_pre_topc(k1_tops_1(sK6,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_3625,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v3_pre_topc(k1_tops_1(sK6,sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3624])).

cnf(c_87,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_83,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_24,negated_conjecture,
    ( sP0(sK7,sK6)
    | v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10417,c_8859,c_6803,c_4278,c_4213,c_4109,c_4105,c_4101,c_4097,c_3850,c_3851,c_3627,c_3625,c_87,c_83,c_24,c_30,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:41:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.86/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.86/0.99  
% 3.86/0.99  ------  iProver source info
% 3.86/0.99  
% 3.86/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.86/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.86/0.99  git: non_committed_changes: false
% 3.86/0.99  git: last_make_outside_of_git: false
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options
% 3.86/0.99  
% 3.86/0.99  --out_options                           all
% 3.86/0.99  --tptp_safe_out                         true
% 3.86/0.99  --problem_path                          ""
% 3.86/0.99  --include_path                          ""
% 3.86/0.99  --clausifier                            res/vclausify_rel
% 3.86/0.99  --clausifier_options                    --mode clausify
% 3.86/0.99  --stdin                                 false
% 3.86/0.99  --stats_out                             all
% 3.86/0.99  
% 3.86/0.99  ------ General Options
% 3.86/0.99  
% 3.86/0.99  --fof                                   false
% 3.86/0.99  --time_out_real                         305.
% 3.86/0.99  --time_out_virtual                      -1.
% 3.86/0.99  --symbol_type_check                     false
% 3.86/0.99  --clausify_out                          false
% 3.86/0.99  --sig_cnt_out                           false
% 3.86/0.99  --trig_cnt_out                          false
% 3.86/0.99  --trig_cnt_out_tolerance                1.
% 3.86/0.99  --trig_cnt_out_sk_spl                   false
% 3.86/0.99  --abstr_cl_out                          false
% 3.86/0.99  
% 3.86/0.99  ------ Global Options
% 3.86/0.99  
% 3.86/0.99  --schedule                              default
% 3.86/0.99  --add_important_lit                     false
% 3.86/0.99  --prop_solver_per_cl                    1000
% 3.86/0.99  --min_unsat_core                        false
% 3.86/0.99  --soft_assumptions                      false
% 3.86/0.99  --soft_lemma_size                       3
% 3.86/0.99  --prop_impl_unit_size                   0
% 3.86/0.99  --prop_impl_unit                        []
% 3.86/0.99  --share_sel_clauses                     true
% 3.86/0.99  --reset_solvers                         false
% 3.86/0.99  --bc_imp_inh                            [conj_cone]
% 3.86/0.99  --conj_cone_tolerance                   3.
% 3.86/0.99  --extra_neg_conj                        none
% 3.86/0.99  --large_theory_mode                     true
% 3.86/0.99  --prolific_symb_bound                   200
% 3.86/0.99  --lt_threshold                          2000
% 3.86/0.99  --clause_weak_htbl                      true
% 3.86/0.99  --gc_record_bc_elim                     false
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing Options
% 3.86/0.99  
% 3.86/0.99  --preprocessing_flag                    true
% 3.86/0.99  --time_out_prep_mult                    0.1
% 3.86/0.99  --splitting_mode                        input
% 3.86/0.99  --splitting_grd                         true
% 3.86/0.99  --splitting_cvd                         false
% 3.86/0.99  --splitting_cvd_svl                     false
% 3.86/0.99  --splitting_nvd                         32
% 3.86/0.99  --sub_typing                            true
% 3.86/0.99  --prep_gs_sim                           true
% 3.86/0.99  --prep_unflatten                        true
% 3.86/0.99  --prep_res_sim                          true
% 3.86/0.99  --prep_upred                            true
% 3.86/0.99  --prep_sem_filter                       exhaustive
% 3.86/0.99  --prep_sem_filter_out                   false
% 3.86/0.99  --pred_elim                             true
% 3.86/0.99  --res_sim_input                         true
% 3.86/0.99  --eq_ax_congr_red                       true
% 3.86/0.99  --pure_diseq_elim                       true
% 3.86/0.99  --brand_transform                       false
% 3.86/0.99  --non_eq_to_eq                          false
% 3.86/0.99  --prep_def_merge                        true
% 3.86/0.99  --prep_def_merge_prop_impl              false
% 3.86/0.99  --prep_def_merge_mbd                    true
% 3.86/0.99  --prep_def_merge_tr_red                 false
% 3.86/0.99  --prep_def_merge_tr_cl                  false
% 3.86/0.99  --smt_preprocessing                     true
% 3.86/0.99  --smt_ac_axioms                         fast
% 3.86/0.99  --preprocessed_out                      false
% 3.86/0.99  --preprocessed_stats                    false
% 3.86/0.99  
% 3.86/0.99  ------ Abstraction refinement Options
% 3.86/0.99  
% 3.86/0.99  --abstr_ref                             []
% 3.86/0.99  --abstr_ref_prep                        false
% 3.86/0.99  --abstr_ref_until_sat                   false
% 3.86/0.99  --abstr_ref_sig_restrict                funpre
% 3.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.86/0.99  --abstr_ref_under                       []
% 3.86/0.99  
% 3.86/0.99  ------ SAT Options
% 3.86/0.99  
% 3.86/0.99  --sat_mode                              false
% 3.86/0.99  --sat_fm_restart_options                ""
% 3.86/0.99  --sat_gr_def                            false
% 3.86/0.99  --sat_epr_types                         true
% 3.86/0.99  --sat_non_cyclic_types                  false
% 3.86/0.99  --sat_finite_models                     false
% 3.86/0.99  --sat_fm_lemmas                         false
% 3.86/0.99  --sat_fm_prep                           false
% 3.86/0.99  --sat_fm_uc_incr                        true
% 3.86/0.99  --sat_out_model                         small
% 3.86/0.99  --sat_out_clauses                       false
% 3.86/0.99  
% 3.86/0.99  ------ QBF Options
% 3.86/0.99  
% 3.86/0.99  --qbf_mode                              false
% 3.86/0.99  --qbf_elim_univ                         false
% 3.86/0.99  --qbf_dom_inst                          none
% 3.86/0.99  --qbf_dom_pre_inst                      false
% 3.86/0.99  --qbf_sk_in                             false
% 3.86/0.99  --qbf_pred_elim                         true
% 3.86/0.99  --qbf_split                             512
% 3.86/0.99  
% 3.86/0.99  ------ BMC1 Options
% 3.86/0.99  
% 3.86/0.99  --bmc1_incremental                      false
% 3.86/0.99  --bmc1_axioms                           reachable_all
% 3.86/0.99  --bmc1_min_bound                        0
% 3.86/0.99  --bmc1_max_bound                        -1
% 3.86/0.99  --bmc1_max_bound_default                -1
% 3.86/0.99  --bmc1_symbol_reachability              true
% 3.86/0.99  --bmc1_property_lemmas                  false
% 3.86/0.99  --bmc1_k_induction                      false
% 3.86/0.99  --bmc1_non_equiv_states                 false
% 3.86/0.99  --bmc1_deadlock                         false
% 3.86/0.99  --bmc1_ucm                              false
% 3.86/0.99  --bmc1_add_unsat_core                   none
% 3.86/0.99  --bmc1_unsat_core_children              false
% 3.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.86/0.99  --bmc1_out_stat                         full
% 3.86/0.99  --bmc1_ground_init                      false
% 3.86/0.99  --bmc1_pre_inst_next_state              false
% 3.86/0.99  --bmc1_pre_inst_state                   false
% 3.86/0.99  --bmc1_pre_inst_reach_state             false
% 3.86/0.99  --bmc1_out_unsat_core                   false
% 3.86/0.99  --bmc1_aig_witness_out                  false
% 3.86/0.99  --bmc1_verbose                          false
% 3.86/0.99  --bmc1_dump_clauses_tptp                false
% 3.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.86/0.99  --bmc1_dump_file                        -
% 3.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.86/0.99  --bmc1_ucm_extend_mode                  1
% 3.86/0.99  --bmc1_ucm_init_mode                    2
% 3.86/0.99  --bmc1_ucm_cone_mode                    none
% 3.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.86/0.99  --bmc1_ucm_relax_model                  4
% 3.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.86/0.99  --bmc1_ucm_layered_model                none
% 3.86/0.99  --bmc1_ucm_max_lemma_size               10
% 3.86/0.99  
% 3.86/0.99  ------ AIG Options
% 3.86/0.99  
% 3.86/0.99  --aig_mode                              false
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation Options
% 3.86/0.99  
% 3.86/0.99  --instantiation_flag                    true
% 3.86/0.99  --inst_sos_flag                         false
% 3.86/0.99  --inst_sos_phase                        true
% 3.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel_side                     num_symb
% 3.86/0.99  --inst_solver_per_active                1400
% 3.86/0.99  --inst_solver_calls_frac                1.
% 3.86/0.99  --inst_passive_queue_type               priority_queues
% 3.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.86/0.99  --inst_passive_queues_freq              [25;2]
% 3.86/0.99  --inst_dismatching                      true
% 3.86/0.99  --inst_eager_unprocessed_to_passive     true
% 3.86/0.99  --inst_prop_sim_given                   true
% 3.86/0.99  --inst_prop_sim_new                     false
% 3.86/0.99  --inst_subs_new                         false
% 3.86/0.99  --inst_eq_res_simp                      false
% 3.86/0.99  --inst_subs_given                       false
% 3.86/0.99  --inst_orphan_elimination               true
% 3.86/0.99  --inst_learning_loop_flag               true
% 3.86/0.99  --inst_learning_start                   3000
% 3.86/0.99  --inst_learning_factor                  2
% 3.86/0.99  --inst_start_prop_sim_after_learn       3
% 3.86/0.99  --inst_sel_renew                        solver
% 3.86/0.99  --inst_lit_activity_flag                true
% 3.86/0.99  --inst_restr_to_given                   false
% 3.86/0.99  --inst_activity_threshold               500
% 3.86/0.99  --inst_out_proof                        true
% 3.86/0.99  
% 3.86/0.99  ------ Resolution Options
% 3.86/0.99  
% 3.86/0.99  --resolution_flag                       true
% 3.86/0.99  --res_lit_sel                           adaptive
% 3.86/0.99  --res_lit_sel_side                      none
% 3.86/0.99  --res_ordering                          kbo
% 3.86/0.99  --res_to_prop_solver                    active
% 3.86/0.99  --res_prop_simpl_new                    false
% 3.86/0.99  --res_prop_simpl_given                  true
% 3.86/0.99  --res_passive_queue_type                priority_queues
% 3.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.86/0.99  --res_passive_queues_freq               [15;5]
% 3.86/0.99  --res_forward_subs                      full
% 3.86/0.99  --res_backward_subs                     full
% 3.86/0.99  --res_forward_subs_resolution           true
% 3.86/0.99  --res_backward_subs_resolution          true
% 3.86/0.99  --res_orphan_elimination                true
% 3.86/0.99  --res_time_limit                        2.
% 3.86/0.99  --res_out_proof                         true
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Options
% 3.86/0.99  
% 3.86/0.99  --superposition_flag                    true
% 3.86/0.99  --sup_passive_queue_type                priority_queues
% 3.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.86/0.99  --demod_completeness_check              fast
% 3.86/0.99  --demod_use_ground                      true
% 3.86/0.99  --sup_to_prop_solver                    passive
% 3.86/0.99  --sup_prop_simpl_new                    true
% 3.86/0.99  --sup_prop_simpl_given                  true
% 3.86/0.99  --sup_fun_splitting                     false
% 3.86/0.99  --sup_smt_interval                      50000
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Simplification Setup
% 3.86/0.99  
% 3.86/0.99  --sup_indices_passive                   []
% 3.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_full_bw                           [BwDemod]
% 3.86/0.99  --sup_immed_triv                        [TrivRules]
% 3.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_immed_bw_main                     []
% 3.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  
% 3.86/0.99  ------ Combination Options
% 3.86/0.99  
% 3.86/0.99  --comb_res_mult                         3
% 3.86/0.99  --comb_sup_mult                         2
% 3.86/0.99  --comb_inst_mult                        10
% 3.86/0.99  
% 3.86/0.99  ------ Debug Options
% 3.86/0.99  
% 3.86/0.99  --dbg_backtrace                         false
% 3.86/0.99  --dbg_dump_prop_clauses                 false
% 3.86/0.99  --dbg_dump_prop_clauses_file            -
% 3.86/0.99  --dbg_out_stat                          false
% 3.86/0.99  ------ Parsing...
% 3.86/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.86/0.99  ------ Proving...
% 3.86/0.99  ------ Problem Properties 
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  clauses                                 25
% 3.86/0.99  conjectures                             3
% 3.86/0.99  EPR                                     5
% 3.86/0.99  Horn                                    19
% 3.86/0.99  unary                                   2
% 3.86/0.99  binary                                  6
% 3.86/0.99  lits                                    74
% 3.86/0.99  lits eq                                 1
% 3.86/0.99  fd_pure                                 0
% 3.86/0.99  fd_pseudo                               0
% 3.86/0.99  fd_cond                                 0
% 3.86/0.99  fd_pseudo_cond                          1
% 3.86/0.99  AC symbols                              0
% 3.86/0.99  
% 3.86/0.99  ------ Schedule dynamic 5 is on 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  Current options:
% 3.86/0.99  ------ 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options
% 3.86/0.99  
% 3.86/0.99  --out_options                           all
% 3.86/0.99  --tptp_safe_out                         true
% 3.86/0.99  --problem_path                          ""
% 3.86/0.99  --include_path                          ""
% 3.86/0.99  --clausifier                            res/vclausify_rel
% 3.86/0.99  --clausifier_options                    --mode clausify
% 3.86/0.99  --stdin                                 false
% 3.86/0.99  --stats_out                             all
% 3.86/0.99  
% 3.86/0.99  ------ General Options
% 3.86/0.99  
% 3.86/0.99  --fof                                   false
% 3.86/0.99  --time_out_real                         305.
% 3.86/0.99  --time_out_virtual                      -1.
% 3.86/0.99  --symbol_type_check                     false
% 3.86/0.99  --clausify_out                          false
% 3.86/0.99  --sig_cnt_out                           false
% 3.86/0.99  --trig_cnt_out                          false
% 3.86/0.99  --trig_cnt_out_tolerance                1.
% 3.86/0.99  --trig_cnt_out_sk_spl                   false
% 3.86/0.99  --abstr_cl_out                          false
% 3.86/0.99  
% 3.86/0.99  ------ Global Options
% 3.86/0.99  
% 3.86/0.99  --schedule                              default
% 3.86/0.99  --add_important_lit                     false
% 3.86/0.99  --prop_solver_per_cl                    1000
% 3.86/0.99  --min_unsat_core                        false
% 3.86/0.99  --soft_assumptions                      false
% 3.86/0.99  --soft_lemma_size                       3
% 3.86/0.99  --prop_impl_unit_size                   0
% 3.86/0.99  --prop_impl_unit                        []
% 3.86/0.99  --share_sel_clauses                     true
% 3.86/0.99  --reset_solvers                         false
% 3.86/0.99  --bc_imp_inh                            [conj_cone]
% 3.86/0.99  --conj_cone_tolerance                   3.
% 3.86/0.99  --extra_neg_conj                        none
% 3.86/0.99  --large_theory_mode                     true
% 3.86/0.99  --prolific_symb_bound                   200
% 3.86/0.99  --lt_threshold                          2000
% 3.86/0.99  --clause_weak_htbl                      true
% 3.86/0.99  --gc_record_bc_elim                     false
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing Options
% 3.86/0.99  
% 3.86/0.99  --preprocessing_flag                    true
% 3.86/0.99  --time_out_prep_mult                    0.1
% 3.86/0.99  --splitting_mode                        input
% 3.86/0.99  --splitting_grd                         true
% 3.86/0.99  --splitting_cvd                         false
% 3.86/0.99  --splitting_cvd_svl                     false
% 3.86/0.99  --splitting_nvd                         32
% 3.86/0.99  --sub_typing                            true
% 3.86/0.99  --prep_gs_sim                           true
% 3.86/0.99  --prep_unflatten                        true
% 3.86/0.99  --prep_res_sim                          true
% 3.86/0.99  --prep_upred                            true
% 3.86/0.99  --prep_sem_filter                       exhaustive
% 3.86/0.99  --prep_sem_filter_out                   false
% 3.86/0.99  --pred_elim                             true
% 3.86/0.99  --res_sim_input                         true
% 3.86/0.99  --eq_ax_congr_red                       true
% 3.86/0.99  --pure_diseq_elim                       true
% 3.86/0.99  --brand_transform                       false
% 3.86/0.99  --non_eq_to_eq                          false
% 3.86/0.99  --prep_def_merge                        true
% 3.86/0.99  --prep_def_merge_prop_impl              false
% 3.86/0.99  --prep_def_merge_mbd                    true
% 3.86/0.99  --prep_def_merge_tr_red                 false
% 3.86/0.99  --prep_def_merge_tr_cl                  false
% 3.86/0.99  --smt_preprocessing                     true
% 3.86/0.99  --smt_ac_axioms                         fast
% 3.86/0.99  --preprocessed_out                      false
% 3.86/0.99  --preprocessed_stats                    false
% 3.86/0.99  
% 3.86/0.99  ------ Abstraction refinement Options
% 3.86/0.99  
% 3.86/0.99  --abstr_ref                             []
% 3.86/0.99  --abstr_ref_prep                        false
% 3.86/0.99  --abstr_ref_until_sat                   false
% 3.86/0.99  --abstr_ref_sig_restrict                funpre
% 3.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.86/0.99  --abstr_ref_under                       []
% 3.86/0.99  
% 3.86/0.99  ------ SAT Options
% 3.86/0.99  
% 3.86/0.99  --sat_mode                              false
% 3.86/0.99  --sat_fm_restart_options                ""
% 3.86/0.99  --sat_gr_def                            false
% 3.86/0.99  --sat_epr_types                         true
% 3.86/0.99  --sat_non_cyclic_types                  false
% 3.86/0.99  --sat_finite_models                     false
% 3.86/0.99  --sat_fm_lemmas                         false
% 3.86/0.99  --sat_fm_prep                           false
% 3.86/0.99  --sat_fm_uc_incr                        true
% 3.86/0.99  --sat_out_model                         small
% 3.86/0.99  --sat_out_clauses                       false
% 3.86/0.99  
% 3.86/0.99  ------ QBF Options
% 3.86/0.99  
% 3.86/0.99  --qbf_mode                              false
% 3.86/0.99  --qbf_elim_univ                         false
% 3.86/0.99  --qbf_dom_inst                          none
% 3.86/0.99  --qbf_dom_pre_inst                      false
% 3.86/0.99  --qbf_sk_in                             false
% 3.86/0.99  --qbf_pred_elim                         true
% 3.86/0.99  --qbf_split                             512
% 3.86/0.99  
% 3.86/0.99  ------ BMC1 Options
% 3.86/0.99  
% 3.86/0.99  --bmc1_incremental                      false
% 3.86/0.99  --bmc1_axioms                           reachable_all
% 3.86/0.99  --bmc1_min_bound                        0
% 3.86/0.99  --bmc1_max_bound                        -1
% 3.86/0.99  --bmc1_max_bound_default                -1
% 3.86/0.99  --bmc1_symbol_reachability              true
% 3.86/0.99  --bmc1_property_lemmas                  false
% 3.86/0.99  --bmc1_k_induction                      false
% 3.86/0.99  --bmc1_non_equiv_states                 false
% 3.86/0.99  --bmc1_deadlock                         false
% 3.86/0.99  --bmc1_ucm                              false
% 3.86/0.99  --bmc1_add_unsat_core                   none
% 3.86/0.99  --bmc1_unsat_core_children              false
% 3.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.86/0.99  --bmc1_out_stat                         full
% 3.86/0.99  --bmc1_ground_init                      false
% 3.86/0.99  --bmc1_pre_inst_next_state              false
% 3.86/0.99  --bmc1_pre_inst_state                   false
% 3.86/0.99  --bmc1_pre_inst_reach_state             false
% 3.86/0.99  --bmc1_out_unsat_core                   false
% 3.86/0.99  --bmc1_aig_witness_out                  false
% 3.86/0.99  --bmc1_verbose                          false
% 3.86/0.99  --bmc1_dump_clauses_tptp                false
% 3.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.86/0.99  --bmc1_dump_file                        -
% 3.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.86/0.99  --bmc1_ucm_extend_mode                  1
% 3.86/0.99  --bmc1_ucm_init_mode                    2
% 3.86/0.99  --bmc1_ucm_cone_mode                    none
% 3.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.86/0.99  --bmc1_ucm_relax_model                  4
% 3.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.86/0.99  --bmc1_ucm_layered_model                none
% 3.86/0.99  --bmc1_ucm_max_lemma_size               10
% 3.86/0.99  
% 3.86/0.99  ------ AIG Options
% 3.86/0.99  
% 3.86/0.99  --aig_mode                              false
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation Options
% 3.86/0.99  
% 3.86/0.99  --instantiation_flag                    true
% 3.86/0.99  --inst_sos_flag                         false
% 3.86/0.99  --inst_sos_phase                        true
% 3.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel_side                     none
% 3.86/0.99  --inst_solver_per_active                1400
% 3.86/0.99  --inst_solver_calls_frac                1.
% 3.86/0.99  --inst_passive_queue_type               priority_queues
% 3.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.86/0.99  --inst_passive_queues_freq              [25;2]
% 3.86/0.99  --inst_dismatching                      true
% 3.86/0.99  --inst_eager_unprocessed_to_passive     true
% 3.86/0.99  --inst_prop_sim_given                   true
% 3.86/0.99  --inst_prop_sim_new                     false
% 3.86/0.99  --inst_subs_new                         false
% 3.86/0.99  --inst_eq_res_simp                      false
% 3.86/0.99  --inst_subs_given                       false
% 3.86/0.99  --inst_orphan_elimination               true
% 3.86/0.99  --inst_learning_loop_flag               true
% 3.86/0.99  --inst_learning_start                   3000
% 3.86/0.99  --inst_learning_factor                  2
% 3.86/0.99  --inst_start_prop_sim_after_learn       3
% 3.86/0.99  --inst_sel_renew                        solver
% 3.86/0.99  --inst_lit_activity_flag                true
% 3.86/0.99  --inst_restr_to_given                   false
% 3.86/0.99  --inst_activity_threshold               500
% 3.86/0.99  --inst_out_proof                        true
% 3.86/0.99  
% 3.86/0.99  ------ Resolution Options
% 3.86/0.99  
% 3.86/0.99  --resolution_flag                       false
% 3.86/0.99  --res_lit_sel                           adaptive
% 3.86/0.99  --res_lit_sel_side                      none
% 3.86/0.99  --res_ordering                          kbo
% 3.86/0.99  --res_to_prop_solver                    active
% 3.86/0.99  --res_prop_simpl_new                    false
% 3.86/0.99  --res_prop_simpl_given                  true
% 3.86/0.99  --res_passive_queue_type                priority_queues
% 3.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.86/0.99  --res_passive_queues_freq               [15;5]
% 3.86/0.99  --res_forward_subs                      full
% 3.86/0.99  --res_backward_subs                     full
% 3.86/0.99  --res_forward_subs_resolution           true
% 3.86/0.99  --res_backward_subs_resolution          true
% 3.86/0.99  --res_orphan_elimination                true
% 3.86/0.99  --res_time_limit                        2.
% 3.86/0.99  --res_out_proof                         true
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Options
% 3.86/0.99  
% 3.86/0.99  --superposition_flag                    true
% 3.86/0.99  --sup_passive_queue_type                priority_queues
% 3.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.86/0.99  --demod_completeness_check              fast
% 3.86/0.99  --demod_use_ground                      true
% 3.86/0.99  --sup_to_prop_solver                    passive
% 3.86/0.99  --sup_prop_simpl_new                    true
% 3.86/0.99  --sup_prop_simpl_given                  true
% 3.86/0.99  --sup_fun_splitting                     false
% 3.86/0.99  --sup_smt_interval                      50000
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Simplification Setup
% 3.86/0.99  
% 3.86/0.99  --sup_indices_passive                   []
% 3.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_full_bw                           [BwDemod]
% 3.86/0.99  --sup_immed_triv                        [TrivRules]
% 3.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_immed_bw_main                     []
% 3.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  
% 3.86/0.99  ------ Combination Options
% 3.86/0.99  
% 3.86/0.99  --comb_res_mult                         3
% 3.86/0.99  --comb_sup_mult                         2
% 3.86/0.99  --comb_inst_mult                        10
% 3.86/0.99  
% 3.86/0.99  ------ Debug Options
% 3.86/0.99  
% 3.86/0.99  --dbg_backtrace                         false
% 3.86/0.99  --dbg_dump_prop_clauses                 false
% 3.86/0.99  --dbg_dump_prop_clauses_file            -
% 3.86/0.99  --dbg_out_stat                          false
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ Proving...
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS status Theorem for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  fof(f5,axiom,(
% 3.86/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f12,plain,(
% 3.86/0.99    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f5])).
% 3.86/0.99  
% 3.86/0.99  fof(f13,plain,(
% 3.86/0.99    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.86/0.99    inference(flattening,[],[f12])).
% 3.86/0.99  
% 3.86/0.99  fof(f24,plain,(
% 3.86/0.99    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.86/0.99    inference(nnf_transformation,[],[f13])).
% 3.86/0.99  
% 3.86/0.99  fof(f25,plain,(
% 3.86/0.99    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.86/0.99    inference(rectify,[],[f24])).
% 3.86/0.99  
% 3.86/0.99  fof(f26,plain,(
% 3.86/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK2(X0,X1,X2)) & r1_tarski(sK2(X0,X1,X2),X2) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f27,plain,(
% 3.86/0.99    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK2(X0,X1,X2)) & r1_tarski(sK2(X0,X1,X2),X2) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 3.86/0.99  
% 3.86/0.99  fof(f51,plain,(
% 3.86/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f27])).
% 3.86/0.99  
% 3.86/0.99  fof(f6,conjecture,(
% 3.86/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f7,negated_conjecture,(
% 3.86/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.86/0.99    inference(negated_conjecture,[],[f6])).
% 3.86/0.99  
% 3.86/0.99  fof(f14,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f7])).
% 3.86/0.99  
% 3.86/0.99  fof(f15,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.86/0.99    inference(flattening,[],[f14])).
% 3.86/0.99  
% 3.86/0.99  fof(f16,plain,(
% 3.86/0.99    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.86/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.86/0.99  
% 3.86/0.99  fof(f17,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.86/0.99    inference(definition_folding,[],[f15,f16])).
% 3.86/0.99  
% 3.86/0.99  fof(f34,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.86/0.99    inference(nnf_transformation,[],[f17])).
% 3.86/0.99  
% 3.86/0.99  fof(f35,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : ((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.86/0.99    inference(flattening,[],[f34])).
% 3.86/0.99  
% 3.86/0.99  fof(f37,plain,(
% 3.86/0.99    ( ! [X0] : (? [X1] : ((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~sP0(sK7,X0) | ~v3_pre_topc(sK7,X0)) & (sP0(sK7,X0) | v3_pre_topc(sK7,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f36,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : ((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~sP0(X1,sK6) | ~v3_pre_topc(X1,sK6)) & (sP0(X1,sK6) | v3_pre_topc(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f38,plain,(
% 3.86/0.99    ((~sP0(sK7,sK6) | ~v3_pre_topc(sK7,sK6)) & (sP0(sK7,sK6) | v3_pre_topc(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f35,f37,f36])).
% 3.86/0.99  
% 3.86/0.99  fof(f62,plain,(
% 3.86/0.99    v2_pre_topc(sK6)),
% 3.86/0.99    inference(cnf_transformation,[],[f38])).
% 3.86/0.99  
% 3.86/0.99  fof(f63,plain,(
% 3.86/0.99    l1_pre_topc(sK6)),
% 3.86/0.99    inference(cnf_transformation,[],[f38])).
% 3.86/0.99  
% 3.86/0.99  fof(f28,plain,(
% 3.86/0.99    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1))) | ~sP0(X1,X0)))),
% 3.86/0.99    inference(nnf_transformation,[],[f16])).
% 3.86/0.99  
% 3.86/0.99  fof(f29,plain,(
% 3.86/0.99    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 3.86/0.99    inference(rectify,[],[f28])).
% 3.86/0.99  
% 3.86/0.99  fof(f32,plain,(
% 3.86/0.99    ! [X5,X1,X0] : (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X5,sK5(X0,X1,X5)) & r1_tarski(sK5(X0,X1,X5),X0) & v3_pre_topc(sK5(X0,X1,X5),X1) & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f31,plain,(
% 3.86/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X2,sK4(X0,X1)) & r1_tarski(sK4(X0,X1),X0) & v3_pre_topc(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f30,plain,(
% 3.86/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0))) => ((! [X3] : (~r2_hidden(sK3(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK3(X0,X1),X0)) & (? [X4] : (r2_hidden(sK3(X0,X1),X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK3(X0,X1),X0))))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f33,plain,(
% 3.86/0.99    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (~r2_hidden(sK3(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK3(X0,X1),X0)) & ((r2_hidden(sK3(X0,X1),sK4(X0,X1)) & r1_tarski(sK4(X0,X1),X0) & v3_pre_topc(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK3(X0,X1),X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((r2_hidden(X5,sK5(X0,X1,X5)) & r1_tarski(sK5(X0,X1,X5),X0) & v3_pre_topc(sK5(X0,X1,X5),X1) & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).
% 3.86/0.99  
% 3.86/0.99  fof(f60,plain,(
% 3.86/0.99    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(sK3(X0,X1),X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f64,plain,(
% 3.86/0.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.86/0.99    inference(cnf_transformation,[],[f38])).
% 3.86/0.99  
% 3.86/0.99  fof(f57,plain,(
% 3.86/0.99    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK3(X0,X1),X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f61,plain,(
% 3.86/0.99    ( ! [X0,X3,X1] : (sP0(X0,X1) | ~r2_hidden(sK3(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK3(X0,X1),X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f1,axiom,(
% 3.86/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f8,plain,(
% 3.86/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f1])).
% 3.86/0.99  
% 3.86/0.99  fof(f18,plain,(
% 3.86/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.86/0.99    inference(nnf_transformation,[],[f8])).
% 3.86/0.99  
% 3.86/0.99  fof(f19,plain,(
% 3.86/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.86/0.99    inference(rectify,[],[f18])).
% 3.86/0.99  
% 3.86/0.99  fof(f20,plain,(
% 3.86/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f21,plain,(
% 3.86/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 3.86/0.99  
% 3.86/0.99  fof(f39,plain,(
% 3.86/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f21])).
% 3.86/0.99  
% 3.86/0.99  fof(f66,plain,(
% 3.86/0.99    ~sP0(sK7,sK6) | ~v3_pre_topc(sK7,sK6)),
% 3.86/0.99    inference(cnf_transformation,[],[f38])).
% 3.86/0.99  
% 3.86/0.99  fof(f2,axiom,(
% 3.86/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f22,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(nnf_transformation,[],[f2])).
% 3.86/0.99  
% 3.86/0.99  fof(f23,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(flattening,[],[f22])).
% 3.86/0.99  
% 3.86/0.99  fof(f42,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.86/0.99    inference(cnf_transformation,[],[f23])).
% 3.86/0.99  
% 3.86/0.99  fof(f68,plain,(
% 3.86/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.86/0.99    inference(equality_resolution,[],[f42])).
% 3.86/0.99  
% 3.86/0.99  fof(f58,plain,(
% 3.86/0.99    ( ! [X0,X1] : (sP0(X0,X1) | v3_pre_topc(sK4(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f59,plain,(
% 3.86/0.99    ( ! [X0,X1] : (sP0(X0,X1) | r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK3(X0,X1),X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f49,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (r1_tarski(sK2(X0,X1,X2),X2) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f27])).
% 3.86/0.99  
% 3.86/0.99  fof(f50,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,sK2(X0,X1,X2)) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f27])).
% 3.86/0.99  
% 3.86/0.99  fof(f40,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f21])).
% 3.86/0.99  
% 3.86/0.99  fof(f41,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f21])).
% 3.86/0.99  
% 3.86/0.99  fof(f44,plain,(
% 3.86/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f23])).
% 3.86/0.99  
% 3.86/0.99  fof(f52,plain,(
% 3.86/0.99    ( ! [X0,X5,X1] : (m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f53,plain,(
% 3.86/0.99    ( ! [X0,X5,X1] : (v3_pre_topc(sK5(X0,X1,X5),X1) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f54,plain,(
% 3.86/0.99    ( ! [X0,X5,X1] : (r1_tarski(sK5(X0,X1,X5),X0) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f55,plain,(
% 3.86/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,sK5(X0,X1,X5)) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f4,axiom,(
% 3.86/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f11,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f4])).
% 3.86/0.99  
% 3.86/0.99  fof(f46,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f11])).
% 3.86/0.99  
% 3.86/0.99  fof(f3,axiom,(
% 3.86/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f9,plain,(
% 3.86/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f3])).
% 3.86/0.99  
% 3.86/0.99  fof(f10,plain,(
% 3.86/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.86/0.99    inference(flattening,[],[f9])).
% 3.86/0.99  
% 3.86/0.99  fof(f45,plain,(
% 3.86/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f10])).
% 3.86/0.99  
% 3.86/0.99  fof(f65,plain,(
% 3.86/0.99    sP0(sK7,sK6) | v3_pre_topc(sK7,sK6)),
% 3.86/0.99    inference(cnf_transformation,[],[f38])).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | ~ v3_pre_topc(X0,X1)
% 3.86/0.99      | ~ r2_hidden(X3,X0)
% 3.86/0.99      | r2_hidden(X3,k1_tops_1(X1,X2))
% 3.86/0.99      | ~ r1_tarski(X0,X2)
% 3.86/0.99      | ~ v2_pre_topc(X1)
% 3.86/0.99      | ~ l1_pre_topc(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_27,negated_conjecture,
% 3.86/0.99      ( v2_pre_topc(sK6) ),
% 3.86/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_440,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | ~ v3_pre_topc(X0,X1)
% 3.86/0.99      | ~ r2_hidden(X3,X0)
% 3.86/0.99      | r2_hidden(X3,k1_tops_1(X1,X2))
% 3.86/0.99      | ~ r1_tarski(X0,X2)
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | sK6 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_441,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ v3_pre_topc(X0,sK6)
% 3.86/0.99      | ~ r2_hidden(X2,X0)
% 3.86/0.99      | r2_hidden(X2,k1_tops_1(sK6,X1))
% 3.86/0.99      | ~ r1_tarski(X0,X1)
% 3.86/0.99      | ~ l1_pre_topc(sK6) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_440]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_26,negated_conjecture,
% 3.86/0.99      ( l1_pre_topc(sK6) ),
% 3.86/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_445,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1)
% 3.86/0.99      | r2_hidden(X2,k1_tops_1(sK6,X1))
% 3.86/0.99      | ~ r2_hidden(X2,X0)
% 3.86/0.99      | ~ v3_pre_topc(X0,sK6)
% 3.86/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_441,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_446,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ v3_pre_topc(X0,sK6)
% 3.86/0.99      | ~ r2_hidden(X2,X0)
% 3.86/0.99      | r2_hidden(X2,k1_tops_1(sK6,X1))
% 3.86/0.99      | ~ r1_tarski(X0,X1) ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_445]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7594,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ m1_subset_1(sK5(sK7,X1,sK1(sK7,k1_tops_1(sK6,sK7))),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ v3_pre_topc(sK5(sK7,X1,sK1(sK7,k1_tops_1(sK6,sK7))),sK6)
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK5(sK7,X1,sK1(sK7,k1_tops_1(sK6,sK7))))
% 3.86/0.99      | r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),k1_tops_1(sK6,X0))
% 3.86/0.99      | ~ r1_tarski(sK5(sK7,X1,sK1(sK7,k1_tops_1(sK6,sK7))),X0) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_446]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10415,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ v3_pre_topc(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),sK6)
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))))
% 3.86/0.99      | r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),k1_tops_1(sK6,sK7))
% 3.86/0.99      | ~ r1_tarski(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_7594]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10417,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ v3_pre_topc(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),sK6)
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))))
% 3.86/0.99      | r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),k1_tops_1(sK6,sK7))
% 3.86/0.99      | ~ r1_tarski(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_10415]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_14,plain,
% 3.86/0.99      ( sP0(X0,X1)
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X0)
% 3.86/0.99      | r2_hidden(sK3(X0,X1),sK4(X0,X1)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3427,plain,
% 3.86/0.99      ( sP0(X0,X1) = iProver_top
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X0) = iProver_top
% 3.86/0.99      | r2_hidden(sK3(X0,X1),sK4(X0,X1)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_25,negated_conjecture,
% 3.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.86/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3416,plain,
% 3.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_17,plain,
% 3.86/0.99      ( sP0(X0,X1)
% 3.86/0.99      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3424,plain,
% 3.86/0.99      ( sP0(X0,X1) = iProver_top
% 3.86/0.99      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13,plain,
% 3.86/0.99      ( sP0(X0,X1)
% 3.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | ~ v3_pre_topc(X2,X1)
% 3.86/0.99      | ~ r2_hidden(sK3(X0,X1),X2)
% 3.86/0.99      | ~ r2_hidden(sK3(X0,X1),X0)
% 3.86/0.99      | ~ r1_tarski(X2,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3428,plain,
% 3.86/0.99      ( sP0(X0,X1) = iProver_top
% 3.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.86/0.99      | v3_pre_topc(X2,X1) != iProver_top
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X0) != iProver_top
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X2) != iProver_top
% 3.86/0.99      | r1_tarski(X2,X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3431,plain,
% 3.86/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.86/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.86/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3564,plain,
% 3.86/0.99      ( sP0(X0,X1) = iProver_top
% 3.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.86/0.99      | v3_pre_topc(X2,X1) != iProver_top
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X2) != iProver_top
% 3.86/0.99      | r1_tarski(X2,X0) != iProver_top ),
% 3.86/0.99      inference(forward_subsumption_resolution,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_3428,c_3431]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5952,plain,
% 3.86/0.99      ( sP0(X0,sK6) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(sK3(X0,sK6),sK7) != iProver_top
% 3.86/0.99      | r1_tarski(sK7,X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3416,c_3564]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6312,plain,
% 3.86/0.99      ( sP0(sK7,sK6) = iProver_top
% 3.86/0.99      | m1_subset_1(sK4(sK7,sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r1_tarski(sK7,sK7) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3424,c_5952]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_23,negated_conjecture,
% 3.86/0.99      ( ~ sP0(sK7,sK6) | ~ v3_pre_topc(sK7,sK6) ),
% 3.86/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_32,plain,
% 3.86/0.99      ( sP0(sK7,sK6) != iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5,plain,
% 3.86/0.99      ( r1_tarski(X0,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5845,plain,
% 3.86/0.99      ( r1_tarski(sK7,sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5848,plain,
% 3.86/0.99      ( r1_tarski(sK7,sK7) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_5845]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7318,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | m1_subset_1(sK4(sK7,sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_6312,c_32,c_5848]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7319,plain,
% 3.86/0.99      ( m1_subset_1(sK4(sK7,sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_7318]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3411,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | v3_pre_topc(X0,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.86/0.99      | r2_hidden(X2,k1_tops_1(sK6,X1)) = iProver_top
% 3.86/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7327,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | v3_pre_topc(sK4(sK7,sK6),sK6) != iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(X1,sK4(sK7,sK6)) != iProver_top
% 3.86/0.99      | r2_hidden(X1,k1_tops_1(sK6,X0)) = iProver_top
% 3.86/0.99      | r1_tarski(sK4(sK7,sK6),X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_7319,c_3411]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_16,plain,
% 3.86/0.99      ( sP0(X0,X1)
% 3.86/0.99      | v3_pre_topc(sK4(X0,X1),X1)
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3425,plain,
% 3.86/0.99      ( sP0(X0,X1) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK4(X0,X1),X1) = iProver_top
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6314,plain,
% 3.86/0.99      ( sP0(sK7,sK6) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK4(sK7,sK6),sK6) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r1_tarski(sK7,sK7) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3425,c_5952]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6665,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | v3_pre_topc(sK4(sK7,sK6),sK6) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_6314,c_32,c_5848]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6666,plain,
% 3.86/0.99      ( v3_pre_topc(sK4(sK7,sK6),sK6) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_6665]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7767,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(X1,sK4(sK7,sK6)) != iProver_top
% 3.86/0.99      | r2_hidden(X1,k1_tops_1(sK6,X0)) = iProver_top
% 3.86/0.99      | r1_tarski(sK4(sK7,sK6),X0) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_7327,c_6666]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7780,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(X0,sK4(sK7,sK6)) != iProver_top
% 3.86/0.99      | r2_hidden(X0,k1_tops_1(sK6,sK7)) = iProver_top
% 3.86/0.99      | r1_tarski(sK4(sK7,sK6),sK7) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3416,c_7767]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15,plain,
% 3.86/0.99      ( sP0(X0,X1)
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X0)
% 3.86/0.99      | r1_tarski(sK4(X0,X1),X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3426,plain,
% 3.86/0.99      ( sP0(X0,X1) = iProver_top
% 3.86/0.99      | r2_hidden(sK3(X0,X1),X0) = iProver_top
% 3.86/0.99      | r1_tarski(sK4(X0,X1),X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6313,plain,
% 3.86/0.99      ( sP0(sK7,sK6) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r1_tarski(sK4(sK7,sK6),sK7) = iProver_top
% 3.86/0.99      | r1_tarski(sK7,sK7) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3426,c_5952]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6656,plain,
% 3.86/0.99      ( r1_tarski(sK4(sK7,sK6),sK7) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_6313,c_32,c_5848]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6657,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r1_tarski(sK4(sK7,sK6),sK7) = iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_6656]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7867,plain,
% 3.86/0.99      ( r2_hidden(X0,k1_tops_1(sK6,sK7)) = iProver_top
% 3.86/0.99      | r2_hidden(X0,sK4(sK7,sK6)) != iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_7780,c_6657]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7868,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(X0,sK4(sK7,sK6)) != iProver_top
% 3.86/0.99      | r2_hidden(X0,k1_tops_1(sK6,sK7)) = iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_7867]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7880,plain,
% 3.86/0.99      ( sP0(sK7,sK6) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(sK3(sK7,sK6),k1_tops_1(sK6,sK7)) = iProver_top
% 3.86/0.99      | r2_hidden(sK3(sK7,sK6),sK7) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3427,c_7868]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_30,plain,
% 3.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4549,plain,
% 3.86/0.99      ( sP0(sK7,sK6)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ v3_pre_topc(X0,sK6)
% 3.86/0.99      | ~ r2_hidden(sK3(sK7,sK6),X0)
% 3.86/0.99      | ~ r2_hidden(sK3(sK7,sK6),sK7)
% 3.86/0.99      | ~ r1_tarski(X0,sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5699,plain,
% 3.86/0.99      ( sP0(sK7,sK6)
% 3.86/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ v3_pre_topc(sK7,sK6)
% 3.86/0.99      | ~ r2_hidden(sK3(sK7,sK6),sK7)
% 3.86/0.99      | ~ r1_tarski(sK7,sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_4549]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5700,plain,
% 3.86/0.99      ( sP0(sK7,sK6) = iProver_top
% 3.86/0.99      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(sK3(sK7,sK6),sK7) != iProver_top
% 3.86/0.99      | r1_tarski(sK7,sK7) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_5699]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8781,plain,
% 3.86/0.99      ( r2_hidden(sK3(sK7,sK6),k1_tops_1(sK6,sK7)) = iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_7880,c_30,c_32,c_5700,c_5848]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8782,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(sK3(sK7,sK6),k1_tops_1(sK6,sK7)) = iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_8781]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.86/0.99      | r1_tarski(sK2(X1,X2,X0),X0)
% 3.86/0.99      | ~ v2_pre_topc(X1)
% 3.86/0.99      | ~ l1_pre_topc(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_398,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.86/0.99      | r1_tarski(sK2(X1,X2,X0),X0)
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | sK6 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_399,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ r2_hidden(X1,k1_tops_1(sK6,X0))
% 3.86/0.99      | r1_tarski(sK2(sK6,X1,X0),X0)
% 3.86/0.99      | ~ l1_pre_topc(sK6) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_398]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_403,plain,
% 3.86/0.99      ( r1_tarski(sK2(sK6,X1,X0),X0)
% 3.86/0.99      | ~ r2_hidden(X1,k1_tops_1(sK6,X0))
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_399,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_404,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ r2_hidden(X1,k1_tops_1(sK6,X0))
% 3.86/0.99      | r1_tarski(sK2(sK6,X1,X0),X0) ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_403]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3413,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | r2_hidden(X1,k1_tops_1(sK6,X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK2(sK6,X1,X0),X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | r2_hidden(X2,sK2(X1,X2,X0))
% 3.86/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.86/0.99      | ~ v2_pre_topc(X1)
% 3.86/0.99      | ~ l1_pre_topc(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_419,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | r2_hidden(X2,sK2(X1,X2,X0))
% 3.86/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | sK6 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_420,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | r2_hidden(X1,sK2(sK6,X1,X0))
% 3.86/0.99      | ~ r2_hidden(X1,k1_tops_1(sK6,X0))
% 3.86/0.99      | ~ l1_pre_topc(sK6) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_419]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_424,plain,
% 3.86/0.99      ( ~ r2_hidden(X1,k1_tops_1(sK6,X0))
% 3.86/0.99      | r2_hidden(X1,sK2(sK6,X1,X0))
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_420,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_425,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | r2_hidden(X1,sK2(sK6,X1,X0))
% 3.86/0.99      | ~ r2_hidden(X1,k1_tops_1(sK6,X0)) ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_424]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3412,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | r2_hidden(X1,sK2(sK6,X1,X0)) = iProver_top
% 3.86/0.99      | r2_hidden(X1,k1_tops_1(sK6,X0)) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4371,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | r2_hidden(X1,X2) = iProver_top
% 3.86/0.99      | r2_hidden(X1,k1_tops_1(sK6,X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK2(sK6,X1,X0),X2) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3412,c_3431]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4640,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.86/0.99      | r2_hidden(X1,k1_tops_1(sK6,X0)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3413,c_4371]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4655,plain,
% 3.86/0.99      ( r2_hidden(X0,k1_tops_1(sK6,sK7)) != iProver_top
% 3.86/0.99      | r2_hidden(X0,sK7) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3416,c_4640]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8788,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(sK3(sK7,sK6),sK7) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_8782,c_4655]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8859,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_8788,c_30,c_32,c_5700,c_5848]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1,plain,
% 3.86/0.99      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3432,plain,
% 3.86/0.99      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 3.86/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3736,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(X1,k1_tops_1(sK6,X0)) = iProver_top
% 3.86/0.99      | r2_hidden(X1,sK7) != iProver_top
% 3.86/0.99      | r1_tarski(sK7,X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3416,c_3411]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4128,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(X0,k1_tops_1(sK6,sK7)) = iProver_top
% 3.86/0.99      | r2_hidden(X0,sK7) != iProver_top
% 3.86/0.99      | r1_tarski(sK7,sK7) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3416,c_3736]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3429,plain,
% 3.86/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4161,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(X0,k1_tops_1(sK6,sK7)) = iProver_top
% 3.86/0.99      | r2_hidden(X0,sK7) != iProver_top ),
% 3.86/0.99      inference(forward_subsumption_resolution,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_4128,c_3429]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_0,plain,
% 3.86/0.99      ( ~ r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3433,plain,
% 3.86/0.99      ( r2_hidden(sK1(X0,X1),X1) != iProver_top
% 3.86/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4165,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r2_hidden(sK1(X0,k1_tops_1(sK6,sK7)),sK7) != iProver_top
% 3.86/0.99      | r1_tarski(X0,k1_tops_1(sK6,sK7)) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_4161,c_3433]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6784,plain,
% 3.86/0.99      ( v3_pre_topc(sK7,sK6) != iProver_top
% 3.86/0.99      | r1_tarski(sK7,k1_tops_1(sK6,sK7)) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3432,c_4165]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6803,plain,
% 3.86/0.99      ( ~ v3_pre_topc(sK7,sK6) | r1_tarski(sK7,k1_tops_1(sK6,sK7)) ),
% 3.86/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6784]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2828,plain,
% 3.86/0.99      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.86/0.99      theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3677,plain,
% 3.86/0.99      ( v3_pre_topc(X0,X1)
% 3.86/0.99      | ~ v3_pre_topc(k1_tops_1(sK6,sK7),sK6)
% 3.86/0.99      | X0 != k1_tops_1(sK6,sK7)
% 3.86/0.99      | X1 != sK6 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2828]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4274,plain,
% 3.86/0.99      ( ~ v3_pre_topc(k1_tops_1(sK6,sK7),sK6)
% 3.86/0.99      | v3_pre_topc(sK7,X0)
% 3.86/0.99      | X0 != sK6
% 3.86/0.99      | sK7 != k1_tops_1(sK6,sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3677]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4276,plain,
% 3.86/0.99      ( X0 != sK6
% 3.86/0.99      | sK7 != k1_tops_1(sK6,sK7)
% 3.86/0.99      | v3_pre_topc(k1_tops_1(sK6,sK7),sK6) != iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_4274]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4278,plain,
% 3.86/0.99      ( sK6 != sK6
% 3.86/0.99      | sK7 != k1_tops_1(sK6,sK7)
% 3.86/0.99      | v3_pre_topc(k1_tops_1(sK6,sK7),sK6) != iProver_top
% 3.86/0.99      | v3_pre_topc(sK7,sK6) = iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_4276]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.86/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3827,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,k1_tops_1(sK6,sK7))
% 3.86/0.99      | ~ r1_tarski(k1_tops_1(sK6,sK7),X0)
% 3.86/0.99      | X0 = k1_tops_1(sK6,sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4213,plain,
% 3.86/0.99      ( ~ r1_tarski(k1_tops_1(sK6,sK7),sK7)
% 3.86/0.99      | ~ r1_tarski(sK7,k1_tops_1(sK6,sK7))
% 3.86/0.99      | sK7 = k1_tops_1(sK6,sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3827]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_22,plain,
% 3.86/0.99      ( ~ sP0(X0,X1)
% 3.86/0.99      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | ~ r2_hidden(X2,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4092,plain,
% 3.86/0.99      ( ~ sP0(sK7,X0)
% 3.86/0.99      | m1_subset_1(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),k1_zfmisc_1(u1_struct_0(X0)))
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4109,plain,
% 3.86/0.99      ( ~ sP0(sK7,sK6)
% 3.86/0.99      | m1_subset_1(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_4092]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_21,plain,
% 3.86/0.99      ( ~ sP0(X0,X1)
% 3.86/0.99      | v3_pre_topc(sK5(X0,X1,X2),X1)
% 3.86/0.99      | ~ r2_hidden(X2,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4093,plain,
% 3.86/0.99      ( ~ sP0(sK7,X0)
% 3.86/0.99      | v3_pre_topc(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),X0)
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4105,plain,
% 3.86/0.99      ( ~ sP0(sK7,sK6)
% 3.86/0.99      | v3_pre_topc(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),sK6)
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_4093]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_20,plain,
% 3.86/0.99      ( ~ sP0(X0,X1) | ~ r2_hidden(X2,X0) | r1_tarski(sK5(X0,X1,X2),X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4094,plain,
% 3.86/0.99      ( ~ sP0(sK7,X0)
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7)
% 3.86/0.99      | r1_tarski(sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4101,plain,
% 3.86/0.99      ( ~ sP0(sK7,sK6)
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7)
% 3.86/0.99      | r1_tarski(sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_4094]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_19,plain,
% 3.86/0.99      ( ~ sP0(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,sK5(X0,X1,X2)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4095,plain,
% 3.86/0.99      ( ~ sP0(sK7,X0)
% 3.86/0.99      | r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK5(sK7,X0,sK1(sK7,k1_tops_1(sK6,sK7))))
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4097,plain,
% 3.86/0.99      ( ~ sP0(sK7,sK6)
% 3.86/0.99      | r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK5(sK7,sK6,sK1(sK7,k1_tops_1(sK6,sK7))))
% 3.86/0.99      | ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_4095]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3850,plain,
% 3.86/0.99      ( r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),sK7)
% 3.86/0.99      | r1_tarski(sK7,k1_tops_1(sK6,sK7)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3851,plain,
% 3.86/0.99      ( ~ r2_hidden(sK1(sK7,k1_tops_1(sK6,sK7)),k1_tops_1(sK6,sK7))
% 3.86/0.99      | r1_tarski(sK7,k1_tops_1(sK6,sK7)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.86/0.99      | ~ l1_pre_topc(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_514,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.86/0.99      | sK6 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_515,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | r1_tarski(k1_tops_1(sK6,X0),X0) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_514]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3627,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | r1_tarski(k1_tops_1(sK6,sK7),sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_515]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | v3_pre_topc(k1_tops_1(X1,X0),X1)
% 3.86/0.99      | ~ v2_pre_topc(X1)
% 3.86/0.99      | ~ l1_pre_topc(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_470,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.86/0.99      | v3_pre_topc(k1_tops_1(X1,X0),X1)
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | sK6 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_27]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_471,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | v3_pre_topc(k1_tops_1(sK6,X0),sK6)
% 3.86/0.99      | ~ l1_pre_topc(sK6) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_470]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_475,plain,
% 3.86/0.99      ( v3_pre_topc(k1_tops_1(sK6,X0),sK6)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_471,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_476,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | v3_pre_topc(k1_tops_1(sK6,X0),sK6) ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_475]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3624,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.86/0.99      | v3_pre_topc(k1_tops_1(sK6,sK7),sK6) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_476]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3625,plain,
% 3.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.86/0.99      | v3_pre_topc(k1_tops_1(sK6,sK7),sK6) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3624]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_87,plain,
% 3.86/0.99      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_83,plain,
% 3.86/0.99      ( r1_tarski(sK6,sK6) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_24,negated_conjecture,
% 3.86/0.99      ( sP0(sK7,sK6) | v3_pre_topc(sK7,sK6) ),
% 3.86/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(contradiction,plain,
% 3.86/0.99      ( $false ),
% 3.86/0.99      inference(minisat,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_10417,c_8859,c_6803,c_4278,c_4213,c_4109,c_4105,
% 3.86/0.99                 c_4101,c_4097,c_3850,c_3851,c_3627,c_3625,c_87,c_83,
% 3.86/0.99                 c_24,c_30,c_25]) ).
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  ------                               Statistics
% 3.86/0.99  
% 3.86/0.99  ------ General
% 3.86/0.99  
% 3.86/0.99  abstr_ref_over_cycles:                  0
% 3.86/0.99  abstr_ref_under_cycles:                 0
% 3.86/0.99  gc_basic_clause_elim:                   0
% 3.86/0.99  forced_gc_time:                         0
% 3.86/0.99  parsing_time:                           0.009
% 3.86/0.99  unif_index_cands_time:                  0.
% 3.86/0.99  unif_index_add_time:                    0.
% 3.86/0.99  orderings_time:                         0.
% 3.86/0.99  out_proof_time:                         0.017
% 3.86/0.99  total_time:                             0.388
% 3.86/0.99  num_of_symbols:                         48
% 3.86/0.99  num_of_terms:                           6130
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing
% 3.86/0.99  
% 3.86/0.99  num_of_splits:                          0
% 3.86/0.99  num_of_split_atoms:                     0
% 3.86/0.99  num_of_reused_defs:                     0
% 3.86/0.99  num_eq_ax_congr_red:                    41
% 3.86/0.99  num_of_sem_filtered_clauses:            1
% 3.86/0.99  num_of_subtypes:                        0
% 3.86/0.99  monotx_restored_types:                  0
% 3.86/0.99  sat_num_of_epr_types:                   0
% 3.86/0.99  sat_num_of_non_cyclic_types:            0
% 3.86/0.99  sat_guarded_non_collapsed_types:        0
% 3.86/0.99  num_pure_diseq_elim:                    0
% 3.86/0.99  simp_replaced_by:                       0
% 3.86/0.99  res_preprocessed:                       125
% 3.86/0.99  prep_upred:                             0
% 3.86/0.99  prep_unflattend:                        105
% 3.86/0.99  smt_new_axioms:                         0
% 3.86/0.99  pred_elim_cands:                        5
% 3.86/0.99  pred_elim:                              2
% 3.86/0.99  pred_elim_cl:                           2
% 3.86/0.99  pred_elim_cycles:                       6
% 3.86/0.99  merged_defs:                            8
% 3.86/0.99  merged_defs_ncl:                        0
% 3.86/0.99  bin_hyper_res:                          8
% 3.86/0.99  prep_cycles:                            4
% 3.86/0.99  pred_elim_time:                         0.07
% 3.86/0.99  splitting_time:                         0.
% 3.86/0.99  sem_filter_time:                        0.
% 3.86/0.99  monotx_time:                            0.
% 3.86/0.99  subtype_inf_time:                       0.
% 3.86/0.99  
% 3.86/0.99  ------ Problem properties
% 3.86/0.99  
% 3.86/0.99  clauses:                                25
% 3.86/0.99  conjectures:                            3
% 3.86/0.99  epr:                                    5
% 3.86/0.99  horn:                                   19
% 3.86/0.99  ground:                                 3
% 3.86/0.99  unary:                                  2
% 3.86/0.99  binary:                                 6
% 3.86/0.99  lits:                                   74
% 3.86/0.99  lits_eq:                                1
% 3.86/0.99  fd_pure:                                0
% 3.86/0.99  fd_pseudo:                              0
% 3.86/0.99  fd_cond:                                0
% 3.86/0.99  fd_pseudo_cond:                         1
% 3.86/0.99  ac_symbols:                             0
% 3.86/0.99  
% 3.86/0.99  ------ Propositional Solver
% 3.86/0.99  
% 3.86/0.99  prop_solver_calls:                      29
% 3.86/0.99  prop_fast_solver_calls:                 1869
% 3.86/0.99  smt_solver_calls:                       0
% 3.86/0.99  smt_fast_solver_calls:                  0
% 3.86/0.99  prop_num_of_clauses:                    2694
% 3.86/0.99  prop_preprocess_simplified:             6923
% 3.86/0.99  prop_fo_subsumed:                       72
% 3.86/0.99  prop_solver_time:                       0.
% 3.86/0.99  smt_solver_time:                        0.
% 3.86/0.99  smt_fast_solver_time:                   0.
% 3.86/0.99  prop_fast_solver_time:                  0.
% 3.86/0.99  prop_unsat_core_time:                   0.
% 3.86/0.99  
% 3.86/0.99  ------ QBF
% 3.86/0.99  
% 3.86/0.99  qbf_q_res:                              0
% 3.86/0.99  qbf_num_tautologies:                    0
% 3.86/0.99  qbf_prep_cycles:                        0
% 3.86/0.99  
% 3.86/0.99  ------ BMC1
% 3.86/0.99  
% 3.86/0.99  bmc1_current_bound:                     -1
% 3.86/0.99  bmc1_last_solved_bound:                 -1
% 3.86/0.99  bmc1_unsat_core_size:                   -1
% 3.86/0.99  bmc1_unsat_core_parents_size:           -1
% 3.86/0.99  bmc1_merge_next_fun:                    0
% 3.86/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation
% 3.86/0.99  
% 3.86/0.99  inst_num_of_clauses:                    605
% 3.86/0.99  inst_num_in_passive:                    193
% 3.86/0.99  inst_num_in_active:                     354
% 3.86/0.99  inst_num_in_unprocessed:                57
% 3.86/0.99  inst_num_of_loops:                      473
% 3.86/0.99  inst_num_of_learning_restarts:          0
% 3.86/0.99  inst_num_moves_active_passive:          113
% 3.86/0.99  inst_lit_activity:                      0
% 3.86/0.99  inst_lit_activity_moves:                0
% 3.86/0.99  inst_num_tautologies:                   0
% 3.86/0.99  inst_num_prop_implied:                  0
% 3.86/0.99  inst_num_existing_simplified:           0
% 3.86/0.99  inst_num_eq_res_simplified:             0
% 3.86/0.99  inst_num_child_elim:                    0
% 3.86/0.99  inst_num_of_dismatching_blockings:      142
% 3.86/0.99  inst_num_of_non_proper_insts:           670
% 3.86/0.99  inst_num_of_duplicates:                 0
% 3.86/0.99  inst_inst_num_from_inst_to_res:         0
% 3.86/0.99  inst_dismatching_checking_time:         0.
% 3.86/0.99  
% 3.86/0.99  ------ Resolution
% 3.86/0.99  
% 3.86/0.99  res_num_of_clauses:                     0
% 3.86/0.99  res_num_in_passive:                     0
% 3.86/0.99  res_num_in_active:                      0
% 3.86/0.99  res_num_of_loops:                       129
% 3.86/0.99  res_forward_subset_subsumed:            124
% 3.86/0.99  res_backward_subset_subsumed:           0
% 3.86/0.99  res_forward_subsumed:                   22
% 3.86/0.99  res_backward_subsumed:                  0
% 3.86/0.99  res_forward_subsumption_resolution:     17
% 3.86/0.99  res_backward_subsumption_resolution:    0
% 3.86/0.99  res_clause_to_clause_subsumption:       1927
% 3.86/0.99  res_orphan_elimination:                 0
% 3.86/0.99  res_tautology_del:                      106
% 3.86/0.99  res_num_eq_res_simplified:              0
% 3.86/0.99  res_num_sel_changes:                    0
% 3.86/0.99  res_moves_from_active_to_pass:          0
% 3.86/0.99  
% 3.86/0.99  ------ Superposition
% 3.86/0.99  
% 3.86/0.99  sup_time_total:                         0.
% 3.86/0.99  sup_time_generating:                    0.
% 3.86/0.99  sup_time_sim_full:                      0.
% 3.86/0.99  sup_time_sim_immed:                     0.
% 3.86/0.99  
% 3.86/0.99  sup_num_of_clauses:                     208
% 3.86/0.99  sup_num_in_active:                      82
% 3.86/0.99  sup_num_in_passive:                     126
% 3.86/0.99  sup_num_of_loops:                       94
% 3.86/0.99  sup_fw_superposition:                   122
% 3.86/0.99  sup_bw_superposition:                   155
% 3.86/0.99  sup_immediate_simplified:               23
% 3.86/0.99  sup_given_eliminated:                   0
% 3.86/0.99  comparisons_done:                       0
% 3.86/0.99  comparisons_avoided:                    0
% 3.86/0.99  
% 3.86/0.99  ------ Simplifications
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  sim_fw_subset_subsumed:                 12
% 3.86/0.99  sim_bw_subset_subsumed:                 26
% 3.86/0.99  sim_fw_subsumed:                        11
% 3.86/0.99  sim_bw_subsumed:                        0
% 3.86/0.99  sim_fw_subsumption_res:                 3
% 3.86/0.99  sim_bw_subsumption_res:                 0
% 3.86/0.99  sim_tautology_del:                      6
% 3.86/0.99  sim_eq_tautology_del:                   3
% 3.86/0.99  sim_eq_res_simp:                        0
% 3.86/0.99  sim_fw_demodulated:                     0
% 3.86/0.99  sim_bw_demodulated:                     0
% 3.86/0.99  sim_light_normalised:                   0
% 3.86/0.99  sim_joinable_taut:                      0
% 3.86/0.99  sim_joinable_simp:                      0
% 3.86/0.99  sim_ac_normalised:                      0
% 3.86/0.99  sim_smt_subsumption:                    0
% 3.86/0.99  
%------------------------------------------------------------------------------
