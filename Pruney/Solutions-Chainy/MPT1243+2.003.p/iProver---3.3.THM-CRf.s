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
% DateTime   : Thu Dec  3 12:14:03 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :  199 (2216 expanded)
%              Number of clauses        :  137 ( 545 expanded)
%              Number of leaves         :   14 ( 567 expanded)
%              Depth                    :   29
%              Number of atoms          :  794 (15242 expanded)
%              Number of equality atoms :  217 ( 790 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

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
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> sP0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f17])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ sP0(X1,X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( sP0(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ sP0(X1,X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( sP0(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f36,plain,
    ( ( ~ sP0(sK6,sK5)
      | ~ v3_pre_topc(sK6,sK5) )
    & ( sP0(sK6,sK5)
      | v3_pre_topc(sK6,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f35,f34])).

fof(f62,plain,
    ( sP0(sK6,sK5)
    | v3_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f30,f29,f28])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( v3_pre_topc(sK4(X0,X1,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,
    ( ~ sP0(sK6,sK5)
    | ~ v3_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_tarski(sK3(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X3)
      | ~ r1_tarski(X3,X0)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v3_pre_topc(sK3(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( r1_tarski(sK4(X0,X1,X5),X0)
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK4(X0,X1,X5))
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7572,plain,
    ( r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),X0)
    | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK4(sK6,X1,sK1(sK6,k1_tops_1(sK5,sK6))))
    | ~ r1_tarski(sK4(sK6,X1,sK1(sK6,k1_tops_1(sK5,sK6))),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_16092,plain,
    ( ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK4(sK6,X0,sK1(sK6,k1_tops_1(sK5,sK6))))
    | r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),k1_tops_1(sK5,sK6))
    | ~ r1_tarski(sK4(sK6,X0,sK1(sK6,k1_tops_1(sK5,sK6))),k1_tops_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_7572])).

cnf(c_16094,plain,
    ( ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))))
    | r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),k1_tops_1(sK5,sK6))
    | ~ r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),k1_tops_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_16092])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3164,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_23,negated_conjecture,
    ( sP0(sK6,sK5)
    | v3_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3147,plain,
    ( sP0(sK6,sK5) = iProver_top
    | v3_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1)
    | v3_pre_topc(sK4(X0,X1,X2),X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3150,plain,
    ( sP0(X0,X1) != iProver_top
    | v3_pre_topc(sK4(X0,X1,X2),X1) = iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3149,plain,
    ( sP0(X0,X1) != iProver_top
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_379,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_380,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK5)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_384,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_380,c_25])).

cnf(c_385,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_384])).

cnf(c_416,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(X1,X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_385,c_25])).

cnf(c_417,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_2517,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_417])).

cnf(c_3144,plain,
    ( k1_tops_1(sK5,X0) = X0
    | v3_pre_topc(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2517])).

cnf(c_2518,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_417])).

cnf(c_2547,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2518])).

cnf(c_2548,plain,
    ( k1_tops_1(sK5,X0) = X0
    | v3_pre_topc(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2517])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3146,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_354,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_355,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK5)
    | k1_tops_1(sK5,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_359,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK5)
    | k1_tops_1(sK5,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_25])).

cnf(c_360,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK5,X0) != X0 ),
    inference(renaming,[status(thm)],[c_359])).

cnf(c_464,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) != X0
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_360])).

cnf(c_465,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_2514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_465])).

cnf(c_3140,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2514])).

cnf(c_3396,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_3140])).

cnf(c_3753,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(X0,sK5) != iProver_top
    | k1_tops_1(sK5,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3144,c_2547,c_2548,c_3396])).

cnf(c_3754,plain,
    ( k1_tops_1(sK5,X0) = X0
    | v3_pre_topc(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3753])).

cnf(c_4197,plain,
    ( k1_tops_1(sK5,sK4(X0,sK5,X1)) = sK4(X0,sK5,X1)
    | sP0(X0,sK5) != iProver_top
    | v3_pre_topc(sK4(X0,sK5,X1),sK5) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3149,c_3754])).

cnf(c_4837,plain,
    ( k1_tops_1(sK5,sK4(X0,sK5,X1)) = sK4(X0,sK5,X1)
    | sP0(X0,sK5) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3150,c_4197])).

cnf(c_5495,plain,
    ( k1_tops_1(sK5,sK4(sK6,sK5,X0)) = sK4(sK6,sK5,X0)
    | v3_pre_topc(sK6,sK5) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3147,c_4837])).

cnf(c_29,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( ~ sP0(sK6,sK5)
    | ~ v3_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,plain,
    ( sP0(sK6,sK5) != iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_205,plain,
    ( ~ sP0(sK6,sK5)
    | ~ v3_pre_topc(sK6,sK5) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_1207,plain,
    ( ~ v3_pre_topc(sK6,sK5)
    | r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(sK3(X0,X1),X0)
    | sK5 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_205])).

cnf(c_1208,plain,
    ( ~ v3_pre_topc(sK6,sK5)
    | r2_hidden(sK2(sK6,sK5),sK6)
    | r1_tarski(sK3(sK6,sK5),sK6) ),
    inference(unflattening,[status(thm)],[c_1207])).

cnf(c_1209,plain,
    ( v3_pre_topc(sK6,sK5) != iProver_top
    | r2_hidden(sK2(sK6,sK5),sK6) = iProver_top
    | r1_tarski(sK3(sK6,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_13,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0)
    | r2_hidden(sK2(X0,X1),sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1220,plain,
    ( ~ v3_pre_topc(sK6,sK5)
    | r2_hidden(sK2(X0,X1),X0)
    | r2_hidden(sK2(X0,X1),sK3(X0,X1))
    | sK5 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_205])).

cnf(c_1221,plain,
    ( ~ v3_pre_topc(sK6,sK5)
    | r2_hidden(sK2(sK6,sK5),sK3(sK6,sK5))
    | r2_hidden(sK2(sK6,sK5),sK6) ),
    inference(unflattening,[status(thm)],[c_1220])).

cnf(c_1222,plain,
    ( v3_pre_topc(sK6,sK5) != iProver_top
    | r2_hidden(sK2(sK6,sK5),sK3(sK6,sK5)) = iProver_top
    | r2_hidden(sK2(sK6,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1221])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3666,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3669,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3666])).

cnf(c_4071,plain,
    ( r2_hidden(sK2(sK6,sK5),X0)
    | ~ r2_hidden(sK2(sK6,sK5),sK3(sK6,sK5))
    | ~ r1_tarski(sK3(sK6,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5148,plain,
    ( ~ r2_hidden(sK2(sK6,sK5),sK3(sK6,sK5))
    | r2_hidden(sK2(sK6,sK5),sK6)
    | ~ r1_tarski(sK3(sK6,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_4071])).

cnf(c_5149,plain,
    ( r2_hidden(sK2(sK6,sK5),sK3(sK6,sK5)) != iProver_top
    | r2_hidden(sK2(sK6,sK5),sK6) = iProver_top
    | r1_tarski(sK3(sK6,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5148])).

cnf(c_12,plain,
    ( sP0(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X0,X1),X2)
    | ~ r2_hidden(sK2(X0,X1),X0)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5046,plain,
    ( sP0(X0,sK5)
    | ~ v3_pre_topc(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK2(X0,sK5),X0)
    | ~ r2_hidden(sK2(X0,sK5),sK6)
    | ~ r1_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5217,plain,
    ( sP0(sK6,sK5)
    | ~ v3_pre_topc(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK2(sK6,sK5),sK6)
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_5046])).

cnf(c_5218,plain,
    ( sP0(sK6,sK5) = iProver_top
    | v3_pre_topc(sK6,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK2(sK6,sK5),sK6) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5217])).

cnf(c_5830,plain,
    ( k1_tops_1(sK5,sK4(sK6,sK5,X0)) = sK4(sK6,sK5,X0)
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5495,c_29,c_31,c_1209,c_1222,c_3669,c_5149,c_5218])).

cnf(c_5838,plain,
    ( k1_tops_1(sK5,sK4(sK6,sK5,sK1(sK6,X0))) = sK4(sK6,sK5,sK1(sK6,X0))
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_5830])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,X0),X0) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_3141,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(k1_tops_1(sK5,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_3403,plain,
    ( r1_tarski(k1_tops_1(sK5,sK6),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_3141])).

cnf(c_3163,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4334,plain,
    ( r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_3163])).

cnf(c_5566,plain,
    ( r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4334,c_3163])).

cnf(c_6715,plain,
    ( r2_hidden(sK1(k1_tops_1(sK5,sK6),X0),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK5,sK6),X0) = iProver_top
    | r1_tarski(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3403,c_5566])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3165,plain,
    ( r2_hidden(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6965,plain,
    ( r1_tarski(k1_tops_1(sK5,sK6),X0) = iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6715,c_3165])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3160,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK5,X0),k1_tops_1(sK5,X1)) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_3142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK5,X0),k1_tops_1(sK5,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3162,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4297,plain,
    ( k1_tops_1(sK5,X0) = k1_tops_1(sK5,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK5,X0),k1_tops_1(sK5,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_3162])).

cnf(c_4592,plain,
    ( k1_tops_1(sK5,X0) = k1_tops_1(sK5,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_4297])).

cnf(c_4694,plain,
    ( k1_tops_1(sK5,X0) = k1_tops_1(sK5,sK6)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_4592])).

cnf(c_4737,plain,
    ( k1_tops_1(sK5,X0) = k1_tops_1(sK5,sK6)
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3160,c_4694])).

cnf(c_7487,plain,
    ( k1_tops_1(sK5,k1_tops_1(sK5,sK6)) = k1_tops_1(sK5,sK6)
    | r1_tarski(k1_tops_1(sK5,sK6),sK6) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK5,sK6)) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6965,c_4737])).

cnf(c_3361,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k1_tops_1(sK5,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_3362,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(k1_tops_1(sK5,sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3361])).

cnf(c_2515,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_465])).

cnf(c_2516,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_465])).

cnf(c_2610,plain,
    ( k1_tops_1(sK5,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2515,c_2516,c_2514])).

cnf(c_2611,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,X0) != X0 ),
    inference(renaming,[status(thm)],[c_2610])).

cnf(c_3364,plain,
    ( v3_pre_topc(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_tops_1(sK5,sK6) != sK6 ),
    inference(instantiation,[status(thm)],[c_2611])).

cnf(c_3365,plain,
    ( k1_tops_1(sK5,sK6) != sK6
    | v3_pre_topc(sK6,sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3364])).

cnf(c_3405,plain,
    ( ~ r1_tarski(k1_tops_1(sK5,sK6),sK6)
    | ~ r1_tarski(sK6,k1_tops_1(sK5,sK6))
    | k1_tops_1(sK5,sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3406,plain,
    ( k1_tops_1(sK5,sK6) = sK6
    | r1_tarski(k1_tops_1(sK5,sK6),sK6) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3405])).

cnf(c_9762,plain,
    ( r1_tarski(sK6,k1_tops_1(sK5,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7487,c_29,c_31,c_1209,c_1222,c_3362,c_3365,c_3406,c_3669,c_5149,c_5218])).

cnf(c_9767,plain,
    ( k1_tops_1(sK5,sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6)))) = sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))) ),
    inference(superposition,[status(thm)],[c_5838,c_9762])).

cnf(c_3161,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6712,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK1(k1_tops_1(sK5,X0),X2),X3) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK5,X1),X3) != iProver_top
    | r1_tarski(k1_tops_1(sK5,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_5566])).

cnf(c_7048,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK1(k1_tops_1(sK5,X0),X1),X2) = iProver_top
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(k1_tops_1(sK5,X0),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK5,sK6),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_6712])).

cnf(c_7141,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(k1_tops_1(sK5,X0),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK5,sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7048,c_3165])).

cnf(c_7184,plain,
    ( r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(k1_tops_1(sK5,X0),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK5,sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3160,c_7141])).

cnf(c_8734,plain,
    ( r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(k1_tops_1(sK5,X0),k1_tops_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3161,c_7184])).

cnf(c_9772,plain,
    ( r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),k1_tops_1(sK5,sK6)) = iProver_top
    | r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),u1_struct_0(sK5)) != iProver_top
    | r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9767,c_8734])).

cnf(c_9882,plain,
    ( r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),k1_tops_1(sK5,sK6))
    | ~ r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),u1_struct_0(sK5))
    | ~ r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9772])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7874,plain,
    ( ~ m1_subset_1(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3412])).

cnf(c_16,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3154,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4975,plain,
    ( k1_tops_1(sK5,sK3(X0,sK5)) = sK3(X0,sK5)
    | sP0(X0,sK5) = iProver_top
    | v3_pre_topc(sK3(X0,sK5),sK5) != iProver_top
    | r2_hidden(sK2(X0,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_3754])).

cnf(c_15,plain,
    ( sP0(X0,X1)
    | v3_pre_topc(sK3(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3155,plain,
    ( sP0(X0,X1) = iProver_top
    | v3_pre_topc(sK3(X0,X1),X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5197,plain,
    ( k1_tops_1(sK5,sK3(X0,sK5)) = sK3(X0,sK5)
    | sP0(X0,sK5) = iProver_top
    | r2_hidden(sK2(X0,sK5),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4975,c_3155])).

cnf(c_5843,plain,
    ( k1_tops_1(sK5,sK4(sK6,sK5,sK2(sK6,sK5))) = sK4(sK6,sK5,sK2(sK6,sK5))
    | k1_tops_1(sK5,sK3(sK6,sK5)) = sK3(sK6,sK5)
    | sP0(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5197,c_5830])).

cnf(c_30,plain,
    ( sP0(sK6,sK5) = iProver_top
    | v3_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6375,plain,
    ( sP0(sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5843,c_29,c_30,c_31,c_1209,c_1222,c_3669,c_5149,c_5218])).

cnf(c_4358,plain,
    ( ~ sP0(sK6,X0)
    | m1_subset_1(sK4(sK6,X0,sK1(sK6,k1_tops_1(sK5,sK6))),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4375,plain,
    ( ~ sP0(sK6,sK5)
    | m1_subset_1(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_4358])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r1_tarski(sK4(X0,X1,X2),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4360,plain,
    ( ~ sP0(sK6,X0)
    | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6)
    | r1_tarski(sK4(sK6,X0,sK1(sK6,k1_tops_1(sK5,sK6))),sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4367,plain,
    ( ~ sP0(sK6,sK5)
    | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6)
    | r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),sK6) ),
    inference(instantiation,[status(thm)],[c_4360])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,sK4(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4361,plain,
    ( ~ sP0(sK6,X0)
    | r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK4(sK6,X0,sK1(sK6,k1_tops_1(sK5,sK6))))
    | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4363,plain,
    ( ~ sP0(sK6,sK5)
    | r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))))
    | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_4361])).

cnf(c_3761,plain,
    ( k1_tops_1(sK5,sK6) = sK6
    | v3_pre_topc(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_3754])).

cnf(c_3775,plain,
    ( ~ v3_pre_topc(sK6,sK5)
    | k1_tops_1(sK5,sK6) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3761])).

cnf(c_3461,plain,
    ( ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),k1_tops_1(sK5,sK6))
    | r1_tarski(sK6,k1_tops_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3462,plain,
    ( r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6)
    | r1_tarski(sK6,k1_tops_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16094,c_9882,c_7874,c_6375,c_4375,c_4367,c_4363,c_3775,c_3461,c_3462,c_3405,c_3365,c_3361,c_31,c_23,c_29,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.38/1.43  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/1.43  
% 7.38/1.43  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.38/1.43  
% 7.38/1.43  ------  iProver source info
% 7.38/1.43  
% 7.38/1.43  git: date: 2020-06-30 10:37:57 +0100
% 7.38/1.43  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.38/1.43  git: non_committed_changes: false
% 7.38/1.43  git: last_make_outside_of_git: false
% 7.38/1.43  
% 7.38/1.43  ------ 
% 7.38/1.43  
% 7.38/1.43  ------ Input Options
% 7.38/1.43  
% 7.38/1.43  --out_options                           all
% 7.38/1.43  --tptp_safe_out                         true
% 7.38/1.43  --problem_path                          ""
% 7.38/1.43  --include_path                          ""
% 7.38/1.43  --clausifier                            res/vclausify_rel
% 7.38/1.43  --clausifier_options                    --mode clausify
% 7.38/1.43  --stdin                                 false
% 7.38/1.43  --stats_out                             all
% 7.38/1.43  
% 7.38/1.43  ------ General Options
% 7.38/1.43  
% 7.38/1.43  --fof                                   false
% 7.38/1.43  --time_out_real                         305.
% 7.38/1.43  --time_out_virtual                      -1.
% 7.38/1.43  --symbol_type_check                     false
% 7.38/1.43  --clausify_out                          false
% 7.38/1.43  --sig_cnt_out                           false
% 7.38/1.43  --trig_cnt_out                          false
% 7.38/1.43  --trig_cnt_out_tolerance                1.
% 7.38/1.43  --trig_cnt_out_sk_spl                   false
% 7.38/1.43  --abstr_cl_out                          false
% 7.38/1.43  
% 7.38/1.43  ------ Global Options
% 7.38/1.43  
% 7.38/1.43  --schedule                              default
% 7.38/1.43  --add_important_lit                     false
% 7.38/1.43  --prop_solver_per_cl                    1000
% 7.38/1.43  --min_unsat_core                        false
% 7.38/1.43  --soft_assumptions                      false
% 7.38/1.43  --soft_lemma_size                       3
% 7.38/1.43  --prop_impl_unit_size                   0
% 7.38/1.43  --prop_impl_unit                        []
% 7.38/1.43  --share_sel_clauses                     true
% 7.38/1.43  --reset_solvers                         false
% 7.38/1.43  --bc_imp_inh                            [conj_cone]
% 7.38/1.43  --conj_cone_tolerance                   3.
% 7.38/1.43  --extra_neg_conj                        none
% 7.38/1.43  --large_theory_mode                     true
% 7.38/1.43  --prolific_symb_bound                   200
% 7.38/1.43  --lt_threshold                          2000
% 7.38/1.43  --clause_weak_htbl                      true
% 7.38/1.43  --gc_record_bc_elim                     false
% 7.38/1.43  
% 7.38/1.43  ------ Preprocessing Options
% 7.38/1.43  
% 7.38/1.43  --preprocessing_flag                    true
% 7.38/1.43  --time_out_prep_mult                    0.1
% 7.38/1.43  --splitting_mode                        input
% 7.38/1.43  --splitting_grd                         true
% 7.38/1.43  --splitting_cvd                         false
% 7.38/1.43  --splitting_cvd_svl                     false
% 7.38/1.43  --splitting_nvd                         32
% 7.38/1.43  --sub_typing                            true
% 7.38/1.43  --prep_gs_sim                           true
% 7.38/1.43  --prep_unflatten                        true
% 7.38/1.43  --prep_res_sim                          true
% 7.38/1.43  --prep_upred                            true
% 7.38/1.43  --prep_sem_filter                       exhaustive
% 7.38/1.43  --prep_sem_filter_out                   false
% 7.38/1.43  --pred_elim                             true
% 7.38/1.43  --res_sim_input                         true
% 7.38/1.43  --eq_ax_congr_red                       true
% 7.38/1.43  --pure_diseq_elim                       true
% 7.38/1.43  --brand_transform                       false
% 7.38/1.43  --non_eq_to_eq                          false
% 7.38/1.43  --prep_def_merge                        true
% 7.38/1.43  --prep_def_merge_prop_impl              false
% 7.38/1.43  --prep_def_merge_mbd                    true
% 7.38/1.43  --prep_def_merge_tr_red                 false
% 7.38/1.43  --prep_def_merge_tr_cl                  false
% 7.38/1.43  --smt_preprocessing                     true
% 7.38/1.43  --smt_ac_axioms                         fast
% 7.38/1.43  --preprocessed_out                      false
% 7.38/1.43  --preprocessed_stats                    false
% 7.38/1.43  
% 7.38/1.43  ------ Abstraction refinement Options
% 7.38/1.43  
% 7.38/1.43  --abstr_ref                             []
% 7.38/1.43  --abstr_ref_prep                        false
% 7.38/1.43  --abstr_ref_until_sat                   false
% 7.38/1.43  --abstr_ref_sig_restrict                funpre
% 7.38/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 7.38/1.43  --abstr_ref_under                       []
% 7.38/1.43  
% 7.38/1.43  ------ SAT Options
% 7.38/1.43  
% 7.38/1.43  --sat_mode                              false
% 7.38/1.43  --sat_fm_restart_options                ""
% 7.38/1.43  --sat_gr_def                            false
% 7.38/1.43  --sat_epr_types                         true
% 7.38/1.43  --sat_non_cyclic_types                  false
% 7.38/1.43  --sat_finite_models                     false
% 7.38/1.43  --sat_fm_lemmas                         false
% 7.38/1.43  --sat_fm_prep                           false
% 7.38/1.43  --sat_fm_uc_incr                        true
% 7.38/1.43  --sat_out_model                         small
% 7.38/1.43  --sat_out_clauses                       false
% 7.38/1.43  
% 7.38/1.43  ------ QBF Options
% 7.38/1.43  
% 7.38/1.43  --qbf_mode                              false
% 7.38/1.43  --qbf_elim_univ                         false
% 7.38/1.43  --qbf_dom_inst                          none
% 7.38/1.43  --qbf_dom_pre_inst                      false
% 7.38/1.43  --qbf_sk_in                             false
% 7.38/1.43  --qbf_pred_elim                         true
% 7.38/1.43  --qbf_split                             512
% 7.38/1.43  
% 7.38/1.43  ------ BMC1 Options
% 7.38/1.43  
% 7.38/1.43  --bmc1_incremental                      false
% 7.38/1.43  --bmc1_axioms                           reachable_all
% 7.38/1.43  --bmc1_min_bound                        0
% 7.38/1.43  --bmc1_max_bound                        -1
% 7.38/1.43  --bmc1_max_bound_default                -1
% 7.38/1.43  --bmc1_symbol_reachability              true
% 7.38/1.43  --bmc1_property_lemmas                  false
% 7.38/1.43  --bmc1_k_induction                      false
% 7.38/1.43  --bmc1_non_equiv_states                 false
% 7.38/1.43  --bmc1_deadlock                         false
% 7.38/1.43  --bmc1_ucm                              false
% 7.38/1.43  --bmc1_add_unsat_core                   none
% 7.38/1.44  --bmc1_unsat_core_children              false
% 7.38/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.38/1.44  --bmc1_out_stat                         full
% 7.38/1.44  --bmc1_ground_init                      false
% 7.38/1.44  --bmc1_pre_inst_next_state              false
% 7.38/1.44  --bmc1_pre_inst_state                   false
% 7.38/1.44  --bmc1_pre_inst_reach_state             false
% 7.38/1.44  --bmc1_out_unsat_core                   false
% 7.38/1.44  --bmc1_aig_witness_out                  false
% 7.38/1.44  --bmc1_verbose                          false
% 7.38/1.44  --bmc1_dump_clauses_tptp                false
% 7.38/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.38/1.44  --bmc1_dump_file                        -
% 7.38/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.38/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.38/1.44  --bmc1_ucm_extend_mode                  1
% 7.38/1.44  --bmc1_ucm_init_mode                    2
% 7.38/1.44  --bmc1_ucm_cone_mode                    none
% 7.38/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.38/1.44  --bmc1_ucm_relax_model                  4
% 7.38/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.38/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.38/1.44  --bmc1_ucm_layered_model                none
% 7.38/1.44  --bmc1_ucm_max_lemma_size               10
% 7.38/1.44  
% 7.38/1.44  ------ AIG Options
% 7.38/1.44  
% 7.38/1.44  --aig_mode                              false
% 7.38/1.44  
% 7.38/1.44  ------ Instantiation Options
% 7.38/1.44  
% 7.38/1.44  --instantiation_flag                    true
% 7.38/1.44  --inst_sos_flag                         false
% 7.38/1.44  --inst_sos_phase                        true
% 7.38/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.38/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.38/1.44  --inst_lit_sel_side                     num_symb
% 7.38/1.44  --inst_solver_per_active                1400
% 7.38/1.44  --inst_solver_calls_frac                1.
% 7.38/1.44  --inst_passive_queue_type               priority_queues
% 7.38/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.38/1.44  --inst_passive_queues_freq              [25;2]
% 7.38/1.44  --inst_dismatching                      true
% 7.38/1.44  --inst_eager_unprocessed_to_passive     true
% 7.38/1.44  --inst_prop_sim_given                   true
% 7.38/1.44  --inst_prop_sim_new                     false
% 7.38/1.44  --inst_subs_new                         false
% 7.38/1.44  --inst_eq_res_simp                      false
% 7.38/1.44  --inst_subs_given                       false
% 7.38/1.44  --inst_orphan_elimination               true
% 7.38/1.44  --inst_learning_loop_flag               true
% 7.38/1.44  --inst_learning_start                   3000
% 7.38/1.44  --inst_learning_factor                  2
% 7.38/1.44  --inst_start_prop_sim_after_learn       3
% 7.38/1.44  --inst_sel_renew                        solver
% 7.38/1.44  --inst_lit_activity_flag                true
% 7.38/1.44  --inst_restr_to_given                   false
% 7.38/1.44  --inst_activity_threshold               500
% 7.38/1.44  --inst_out_proof                        true
% 7.38/1.44  
% 7.38/1.44  ------ Resolution Options
% 7.38/1.44  
% 7.38/1.44  --resolution_flag                       true
% 7.38/1.44  --res_lit_sel                           adaptive
% 7.38/1.44  --res_lit_sel_side                      none
% 7.38/1.44  --res_ordering                          kbo
% 7.38/1.44  --res_to_prop_solver                    active
% 7.38/1.44  --res_prop_simpl_new                    false
% 7.38/1.44  --res_prop_simpl_given                  true
% 7.38/1.44  --res_passive_queue_type                priority_queues
% 7.38/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.38/1.44  --res_passive_queues_freq               [15;5]
% 7.38/1.44  --res_forward_subs                      full
% 7.38/1.44  --res_backward_subs                     full
% 7.38/1.44  --res_forward_subs_resolution           true
% 7.38/1.44  --res_backward_subs_resolution          true
% 7.38/1.44  --res_orphan_elimination                true
% 7.38/1.44  --res_time_limit                        2.
% 7.38/1.44  --res_out_proof                         true
% 7.38/1.44  
% 7.38/1.44  ------ Superposition Options
% 7.38/1.44  
% 7.38/1.44  --superposition_flag                    true
% 7.38/1.44  --sup_passive_queue_type                priority_queues
% 7.38/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.38/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.38/1.44  --demod_completeness_check              fast
% 7.38/1.44  --demod_use_ground                      true
% 7.38/1.44  --sup_to_prop_solver                    passive
% 7.38/1.44  --sup_prop_simpl_new                    true
% 7.38/1.44  --sup_prop_simpl_given                  true
% 7.38/1.44  --sup_fun_splitting                     false
% 7.38/1.44  --sup_smt_interval                      50000
% 7.38/1.44  
% 7.38/1.44  ------ Superposition Simplification Setup
% 7.38/1.44  
% 7.38/1.44  --sup_indices_passive                   []
% 7.38/1.44  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.44  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.38/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.44  --sup_full_bw                           [BwDemod]
% 7.38/1.44  --sup_immed_triv                        [TrivRules]
% 7.38/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.44  --sup_immed_bw_main                     []
% 7.38/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.38/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.44  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.44  
% 7.38/1.44  ------ Combination Options
% 7.38/1.44  
% 7.38/1.44  --comb_res_mult                         3
% 7.38/1.44  --comb_sup_mult                         2
% 7.38/1.44  --comb_inst_mult                        10
% 7.38/1.44  
% 7.38/1.44  ------ Debug Options
% 7.38/1.44  
% 7.38/1.44  --dbg_backtrace                         false
% 7.38/1.44  --dbg_dump_prop_clauses                 false
% 7.38/1.44  --dbg_dump_prop_clauses_file            -
% 7.38/1.44  --dbg_out_stat                          false
% 7.38/1.44  ------ Parsing...
% 7.38/1.44  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.38/1.44  
% 7.38/1.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.38/1.44  
% 7.38/1.44  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.38/1.44  
% 7.38/1.44  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.38/1.44  ------ Proving...
% 7.38/1.44  ------ Problem Properties 
% 7.38/1.44  
% 7.38/1.44  
% 7.38/1.44  clauses                                 28
% 7.38/1.44  conjectures                             3
% 7.38/1.44  EPR                                     7
% 7.38/1.44  Horn                                    20
% 7.38/1.44  unary                                   2
% 7.38/1.44  binary                                  11
% 7.38/1.44  lits                                    78
% 7.38/1.44  lits eq                                 3
% 7.38/1.44  fd_pure                                 0
% 7.38/1.44  fd_pseudo                               0
% 7.38/1.44  fd_cond                                 0
% 7.38/1.44  fd_pseudo_cond                          1
% 7.38/1.44  AC symbols                              0
% 7.38/1.44  
% 7.38/1.44  ------ Schedule dynamic 5 is on 
% 7.38/1.44  
% 7.38/1.44  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.38/1.44  
% 7.38/1.44  
% 7.38/1.44  ------ 
% 7.38/1.44  Current options:
% 7.38/1.44  ------ 
% 7.38/1.44  
% 7.38/1.44  ------ Input Options
% 7.38/1.44  
% 7.38/1.44  --out_options                           all
% 7.38/1.44  --tptp_safe_out                         true
% 7.38/1.44  --problem_path                          ""
% 7.38/1.44  --include_path                          ""
% 7.38/1.44  --clausifier                            res/vclausify_rel
% 7.38/1.44  --clausifier_options                    --mode clausify
% 7.38/1.44  --stdin                                 false
% 7.38/1.44  --stats_out                             all
% 7.38/1.44  
% 7.38/1.44  ------ General Options
% 7.38/1.44  
% 7.38/1.44  --fof                                   false
% 7.38/1.44  --time_out_real                         305.
% 7.38/1.44  --time_out_virtual                      -1.
% 7.38/1.44  --symbol_type_check                     false
% 7.38/1.44  --clausify_out                          false
% 7.38/1.44  --sig_cnt_out                           false
% 7.38/1.44  --trig_cnt_out                          false
% 7.38/1.44  --trig_cnt_out_tolerance                1.
% 7.38/1.44  --trig_cnt_out_sk_spl                   false
% 7.38/1.44  --abstr_cl_out                          false
% 7.38/1.44  
% 7.38/1.44  ------ Global Options
% 7.38/1.44  
% 7.38/1.44  --schedule                              default
% 7.38/1.44  --add_important_lit                     false
% 7.38/1.44  --prop_solver_per_cl                    1000
% 7.38/1.44  --min_unsat_core                        false
% 7.38/1.44  --soft_assumptions                      false
% 7.38/1.44  --soft_lemma_size                       3
% 7.38/1.44  --prop_impl_unit_size                   0
% 7.38/1.44  --prop_impl_unit                        []
% 7.38/1.44  --share_sel_clauses                     true
% 7.38/1.44  --reset_solvers                         false
% 7.38/1.44  --bc_imp_inh                            [conj_cone]
% 7.38/1.44  --conj_cone_tolerance                   3.
% 7.38/1.44  --extra_neg_conj                        none
% 7.38/1.44  --large_theory_mode                     true
% 7.38/1.44  --prolific_symb_bound                   200
% 7.38/1.44  --lt_threshold                          2000
% 7.38/1.44  --clause_weak_htbl                      true
% 7.38/1.44  --gc_record_bc_elim                     false
% 7.38/1.44  
% 7.38/1.44  ------ Preprocessing Options
% 7.38/1.44  
% 7.38/1.44  --preprocessing_flag                    true
% 7.38/1.44  --time_out_prep_mult                    0.1
% 7.38/1.44  --splitting_mode                        input
% 7.38/1.44  --splitting_grd                         true
% 7.38/1.44  --splitting_cvd                         false
% 7.38/1.44  --splitting_cvd_svl                     false
% 7.38/1.44  --splitting_nvd                         32
% 7.38/1.44  --sub_typing                            true
% 7.38/1.44  --prep_gs_sim                           true
% 7.38/1.44  --prep_unflatten                        true
% 7.38/1.44  --prep_res_sim                          true
% 7.38/1.44  --prep_upred                            true
% 7.38/1.44  --prep_sem_filter                       exhaustive
% 7.38/1.44  --prep_sem_filter_out                   false
% 7.38/1.44  --pred_elim                             true
% 7.38/1.44  --res_sim_input                         true
% 7.38/1.44  --eq_ax_congr_red                       true
% 7.38/1.44  --pure_diseq_elim                       true
% 7.38/1.44  --brand_transform                       false
% 7.38/1.44  --non_eq_to_eq                          false
% 7.38/1.44  --prep_def_merge                        true
% 7.38/1.44  --prep_def_merge_prop_impl              false
% 7.38/1.44  --prep_def_merge_mbd                    true
% 7.38/1.44  --prep_def_merge_tr_red                 false
% 7.38/1.44  --prep_def_merge_tr_cl                  false
% 7.38/1.44  --smt_preprocessing                     true
% 7.38/1.44  --smt_ac_axioms                         fast
% 7.38/1.44  --preprocessed_out                      false
% 7.38/1.44  --preprocessed_stats                    false
% 7.38/1.44  
% 7.38/1.44  ------ Abstraction refinement Options
% 7.38/1.44  
% 7.38/1.44  --abstr_ref                             []
% 7.38/1.44  --abstr_ref_prep                        false
% 7.38/1.44  --abstr_ref_until_sat                   false
% 7.38/1.44  --abstr_ref_sig_restrict                funpre
% 7.38/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.38/1.44  --abstr_ref_under                       []
% 7.38/1.44  
% 7.38/1.44  ------ SAT Options
% 7.38/1.44  
% 7.38/1.44  --sat_mode                              false
% 7.38/1.44  --sat_fm_restart_options                ""
% 7.38/1.44  --sat_gr_def                            false
% 7.38/1.44  --sat_epr_types                         true
% 7.38/1.44  --sat_non_cyclic_types                  false
% 7.38/1.44  --sat_finite_models                     false
% 7.38/1.44  --sat_fm_lemmas                         false
% 7.38/1.44  --sat_fm_prep                           false
% 7.38/1.44  --sat_fm_uc_incr                        true
% 7.38/1.44  --sat_out_model                         small
% 7.38/1.44  --sat_out_clauses                       false
% 7.38/1.44  
% 7.38/1.44  ------ QBF Options
% 7.38/1.44  
% 7.38/1.44  --qbf_mode                              false
% 7.38/1.44  --qbf_elim_univ                         false
% 7.38/1.44  --qbf_dom_inst                          none
% 7.38/1.44  --qbf_dom_pre_inst                      false
% 7.38/1.44  --qbf_sk_in                             false
% 7.38/1.44  --qbf_pred_elim                         true
% 7.38/1.44  --qbf_split                             512
% 7.38/1.44  
% 7.38/1.44  ------ BMC1 Options
% 7.38/1.44  
% 7.38/1.44  --bmc1_incremental                      false
% 7.38/1.44  --bmc1_axioms                           reachable_all
% 7.38/1.44  --bmc1_min_bound                        0
% 7.38/1.44  --bmc1_max_bound                        -1
% 7.38/1.44  --bmc1_max_bound_default                -1
% 7.38/1.44  --bmc1_symbol_reachability              true
% 7.38/1.44  --bmc1_property_lemmas                  false
% 7.38/1.44  --bmc1_k_induction                      false
% 7.38/1.44  --bmc1_non_equiv_states                 false
% 7.38/1.44  --bmc1_deadlock                         false
% 7.38/1.44  --bmc1_ucm                              false
% 7.38/1.44  --bmc1_add_unsat_core                   none
% 7.38/1.44  --bmc1_unsat_core_children              false
% 7.38/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.38/1.44  --bmc1_out_stat                         full
% 7.38/1.44  --bmc1_ground_init                      false
% 7.38/1.44  --bmc1_pre_inst_next_state              false
% 7.38/1.44  --bmc1_pre_inst_state                   false
% 7.38/1.44  --bmc1_pre_inst_reach_state             false
% 7.38/1.44  --bmc1_out_unsat_core                   false
% 7.38/1.44  --bmc1_aig_witness_out                  false
% 7.38/1.44  --bmc1_verbose                          false
% 7.38/1.44  --bmc1_dump_clauses_tptp                false
% 7.38/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.38/1.44  --bmc1_dump_file                        -
% 7.38/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.38/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.38/1.44  --bmc1_ucm_extend_mode                  1
% 7.38/1.44  --bmc1_ucm_init_mode                    2
% 7.38/1.44  --bmc1_ucm_cone_mode                    none
% 7.38/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.38/1.44  --bmc1_ucm_relax_model                  4
% 7.38/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.38/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.38/1.44  --bmc1_ucm_layered_model                none
% 7.38/1.44  --bmc1_ucm_max_lemma_size               10
% 7.38/1.44  
% 7.38/1.44  ------ AIG Options
% 7.38/1.44  
% 7.38/1.44  --aig_mode                              false
% 7.38/1.44  
% 7.38/1.44  ------ Instantiation Options
% 7.38/1.44  
% 7.38/1.44  --instantiation_flag                    true
% 7.38/1.44  --inst_sos_flag                         false
% 7.38/1.44  --inst_sos_phase                        true
% 7.38/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.38/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.38/1.44  --inst_lit_sel_side                     none
% 7.38/1.44  --inst_solver_per_active                1400
% 7.38/1.44  --inst_solver_calls_frac                1.
% 7.38/1.44  --inst_passive_queue_type               priority_queues
% 7.38/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.38/1.44  --inst_passive_queues_freq              [25;2]
% 7.38/1.44  --inst_dismatching                      true
% 7.38/1.44  --inst_eager_unprocessed_to_passive     true
% 7.38/1.44  --inst_prop_sim_given                   true
% 7.38/1.44  --inst_prop_sim_new                     false
% 7.38/1.44  --inst_subs_new                         false
% 7.38/1.44  --inst_eq_res_simp                      false
% 7.38/1.44  --inst_subs_given                       false
% 7.38/1.44  --inst_orphan_elimination               true
% 7.38/1.44  --inst_learning_loop_flag               true
% 7.38/1.44  --inst_learning_start                   3000
% 7.38/1.44  --inst_learning_factor                  2
% 7.38/1.44  --inst_start_prop_sim_after_learn       3
% 7.38/1.44  --inst_sel_renew                        solver
% 7.38/1.44  --inst_lit_activity_flag                true
% 7.38/1.44  --inst_restr_to_given                   false
% 7.38/1.44  --inst_activity_threshold               500
% 7.38/1.44  --inst_out_proof                        true
% 7.38/1.44  
% 7.38/1.44  ------ Resolution Options
% 7.38/1.44  
% 7.38/1.44  --resolution_flag                       false
% 7.38/1.44  --res_lit_sel                           adaptive
% 7.38/1.44  --res_lit_sel_side                      none
% 7.38/1.44  --res_ordering                          kbo
% 7.38/1.44  --res_to_prop_solver                    active
% 7.38/1.44  --res_prop_simpl_new                    false
% 7.38/1.44  --res_prop_simpl_given                  true
% 7.38/1.44  --res_passive_queue_type                priority_queues
% 7.38/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.38/1.44  --res_passive_queues_freq               [15;5]
% 7.38/1.44  --res_forward_subs                      full
% 7.38/1.44  --res_backward_subs                     full
% 7.38/1.44  --res_forward_subs_resolution           true
% 7.38/1.44  --res_backward_subs_resolution          true
% 7.38/1.44  --res_orphan_elimination                true
% 7.38/1.44  --res_time_limit                        2.
% 7.38/1.44  --res_out_proof                         true
% 7.38/1.44  
% 7.38/1.44  ------ Superposition Options
% 7.38/1.44  
% 7.38/1.44  --superposition_flag                    true
% 7.38/1.44  --sup_passive_queue_type                priority_queues
% 7.38/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.38/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.38/1.44  --demod_completeness_check              fast
% 7.38/1.44  --demod_use_ground                      true
% 7.38/1.44  --sup_to_prop_solver                    passive
% 7.38/1.44  --sup_prop_simpl_new                    true
% 7.38/1.44  --sup_prop_simpl_given                  true
% 7.38/1.44  --sup_fun_splitting                     false
% 7.38/1.44  --sup_smt_interval                      50000
% 7.38/1.44  
% 7.38/1.44  ------ Superposition Simplification Setup
% 7.38/1.44  
% 7.38/1.44  --sup_indices_passive                   []
% 7.38/1.44  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.44  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.38/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.44  --sup_full_bw                           [BwDemod]
% 7.38/1.44  --sup_immed_triv                        [TrivRules]
% 7.38/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.44  --sup_immed_bw_main                     []
% 7.38/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.38/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.44  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.44  
% 7.38/1.44  ------ Combination Options
% 7.38/1.44  
% 7.38/1.44  --comb_res_mult                         3
% 7.38/1.44  --comb_sup_mult                         2
% 7.38/1.44  --comb_inst_mult                        10
% 7.38/1.44  
% 7.38/1.44  ------ Debug Options
% 7.38/1.44  
% 7.38/1.44  --dbg_backtrace                         false
% 7.38/1.44  --dbg_dump_prop_clauses                 false
% 7.38/1.44  --dbg_dump_prop_clauses_file            -
% 7.38/1.44  --dbg_out_stat                          false
% 7.38/1.44  
% 7.38/1.44  
% 7.38/1.44  
% 7.38/1.44  
% 7.38/1.44  ------ Proving...
% 7.38/1.44  
% 7.38/1.44  
% 7.38/1.44  % SZS status Theorem for theBenchmark.p
% 7.38/1.44  
% 7.38/1.44  % SZS output start CNFRefutation for theBenchmark.p
% 7.38/1.44  
% 7.38/1.44  fof(f1,axiom,(
% 7.38/1.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.38/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.38/1.44  
% 7.38/1.44  fof(f9,plain,(
% 7.38/1.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.38/1.44    inference(ennf_transformation,[],[f1])).
% 7.38/1.44  
% 7.38/1.44  fof(f19,plain,(
% 7.38/1.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.38/1.44    inference(nnf_transformation,[],[f9])).
% 7.38/1.44  
% 7.38/1.44  fof(f20,plain,(
% 7.38/1.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.38/1.44    inference(rectify,[],[f19])).
% 7.38/1.44  
% 7.38/1.44  fof(f21,plain,(
% 7.38/1.44    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.38/1.44    introduced(choice_axiom,[])).
% 7.38/1.44  
% 7.38/1.44  fof(f22,plain,(
% 7.38/1.44    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.38/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 7.38/1.44  
% 7.38/1.44  fof(f37,plain,(
% 7.38/1.44    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f22])).
% 7.38/1.44  
% 7.38/1.44  fof(f38,plain,(
% 7.38/1.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f22])).
% 7.38/1.44  
% 7.38/1.44  fof(f7,conjecture,(
% 7.38/1.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 7.38/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.38/1.44  
% 7.38/1.44  fof(f8,negated_conjecture,(
% 7.38/1.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 7.38/1.44    inference(negated_conjecture,[],[f7])).
% 7.38/1.44  
% 7.38/1.44  fof(f15,plain,(
% 7.38/1.44    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.38/1.44    inference(ennf_transformation,[],[f8])).
% 7.38/1.44  
% 7.38/1.44  fof(f16,plain,(
% 7.38/1.44    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.38/1.44    inference(flattening,[],[f15])).
% 7.38/1.44  
% 7.38/1.44  fof(f17,plain,(
% 7.38/1.44    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.38/1.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.38/1.44  
% 7.38/1.44  fof(f18,plain,(
% 7.38/1.44    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.38/1.44    inference(definition_folding,[],[f16,f17])).
% 7.38/1.44  
% 7.38/1.44  fof(f32,plain,(
% 7.38/1.44    ? [X0] : (? [X1] : (((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.38/1.44    inference(nnf_transformation,[],[f18])).
% 7.38/1.44  
% 7.38/1.44  fof(f33,plain,(
% 7.38/1.44    ? [X0] : (? [X1] : ((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.38/1.44    inference(flattening,[],[f32])).
% 7.38/1.44  
% 7.38/1.44  fof(f35,plain,(
% 7.38/1.44    ( ! [X0] : (? [X1] : ((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~sP0(sK6,X0) | ~v3_pre_topc(sK6,X0)) & (sP0(sK6,X0) | v3_pre_topc(sK6,X0)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.38/1.44    introduced(choice_axiom,[])).
% 7.38/1.44  
% 7.38/1.44  fof(f34,plain,(
% 7.38/1.44    ? [X0] : (? [X1] : ((~sP0(X1,X0) | ~v3_pre_topc(X1,X0)) & (sP0(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~sP0(X1,sK5) | ~v3_pre_topc(X1,sK5)) & (sP0(X1,sK5) | v3_pre_topc(X1,sK5)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 7.38/1.44    introduced(choice_axiom,[])).
% 7.38/1.44  
% 7.38/1.44  fof(f36,plain,(
% 7.38/1.44    ((~sP0(sK6,sK5) | ~v3_pre_topc(sK6,sK5)) & (sP0(sK6,sK5) | v3_pre_topc(sK6,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5) & v2_pre_topc(sK5)),
% 7.38/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f35,f34])).
% 7.38/1.44  
% 7.38/1.44  fof(f62,plain,(
% 7.38/1.44    sP0(sK6,sK5) | v3_pre_topc(sK6,sK5)),
% 7.38/1.44    inference(cnf_transformation,[],[f36])).
% 7.38/1.44  
% 7.38/1.44  fof(f26,plain,(
% 7.38/1.44    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1))) | ~sP0(X1,X0)))),
% 7.38/1.44    inference(nnf_transformation,[],[f17])).
% 7.38/1.44  
% 7.38/1.44  fof(f27,plain,(
% 7.38/1.44    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 7.38/1.44    inference(rectify,[],[f26])).
% 7.38/1.44  
% 7.38/1.44  fof(f30,plain,(
% 7.38/1.44    ! [X5,X1,X0] : (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X5,sK4(X0,X1,X5)) & r1_tarski(sK4(X0,X1,X5),X0) & v3_pre_topc(sK4(X0,X1,X5),X1) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.38/1.44    introduced(choice_axiom,[])).
% 7.38/1.44  
% 7.38/1.44  fof(f29,plain,(
% 7.38/1.44    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X2,sK3(X0,X1)) & r1_tarski(sK3(X0,X1),X0) & v3_pre_topc(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 7.38/1.44    introduced(choice_axiom,[])).
% 7.38/1.44  
% 7.38/1.44  fof(f28,plain,(
% 7.38/1.44    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0))) => ((! [X3] : (~r2_hidden(sK2(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),X0)) & (? [X4] : (r2_hidden(sK2(X0,X1),X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),X0))))),
% 7.38/1.44    introduced(choice_axiom,[])).
% 7.38/1.44  
% 7.38/1.44  fof(f31,plain,(
% 7.38/1.44    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (~r2_hidden(sK2(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),X0)) & ((r2_hidden(sK2(X0,X1),sK3(X0,X1)) & r1_tarski(sK3(X0,X1),X0) & v3_pre_topc(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((r2_hidden(X5,sK4(X0,X1,X5)) & r1_tarski(sK4(X0,X1,X5),X0) & v3_pre_topc(sK4(X0,X1,X5),X1) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 7.38/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f30,f29,f28])).
% 7.38/1.44  
% 7.38/1.44  fof(f50,plain,(
% 7.38/1.44    ( ! [X0,X5,X1] : (v3_pre_topc(sK4(X0,X1,X5),X1) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f31])).
% 7.38/1.44  
% 7.38/1.44  fof(f49,plain,(
% 7.38/1.44    ( ! [X0,X5,X1] : (m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f31])).
% 7.38/1.44  
% 7.38/1.44  fof(f6,axiom,(
% 7.38/1.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 7.38/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.38/1.44  
% 7.38/1.44  fof(f13,plain,(
% 7.38/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.38/1.44    inference(ennf_transformation,[],[f6])).
% 7.38/1.44  
% 7.38/1.44  fof(f14,plain,(
% 7.38/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.38/1.44    inference(flattening,[],[f13])).
% 7.38/1.44  
% 7.38/1.44  fof(f47,plain,(
% 7.38/1.44    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f14])).
% 7.38/1.44  
% 7.38/1.44  fof(f59,plain,(
% 7.38/1.44    v2_pre_topc(sK5)),
% 7.38/1.44    inference(cnf_transformation,[],[f36])).
% 7.38/1.44  
% 7.38/1.44  fof(f60,plain,(
% 7.38/1.44    l1_pre_topc(sK5)),
% 7.38/1.44    inference(cnf_transformation,[],[f36])).
% 7.38/1.44  
% 7.38/1.44  fof(f61,plain,(
% 7.38/1.44    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 7.38/1.44    inference(cnf_transformation,[],[f36])).
% 7.38/1.44  
% 7.38/1.44  fof(f48,plain,(
% 7.38/1.44    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f14])).
% 7.38/1.44  
% 7.38/1.44  fof(f63,plain,(
% 7.38/1.44    ~sP0(sK6,sK5) | ~v3_pre_topc(sK6,sK5)),
% 7.38/1.44    inference(cnf_transformation,[],[f36])).
% 7.38/1.44  
% 7.38/1.44  fof(f56,plain,(
% 7.38/1.44    ( ! [X0,X1] : (sP0(X0,X1) | r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK2(X0,X1),X0)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f31])).
% 7.38/1.44  
% 7.38/1.44  fof(f57,plain,(
% 7.38/1.44    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(sK2(X0,X1),X0)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f31])).
% 7.38/1.44  
% 7.38/1.44  fof(f2,axiom,(
% 7.38/1.44    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.38/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.38/1.44  
% 7.38/1.44  fof(f23,plain,(
% 7.38/1.44    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.38/1.44    inference(nnf_transformation,[],[f2])).
% 7.38/1.44  
% 7.38/1.44  fof(f24,plain,(
% 7.38/1.44    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.38/1.44    inference(flattening,[],[f23])).
% 7.38/1.44  
% 7.38/1.44  fof(f40,plain,(
% 7.38/1.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.38/1.44    inference(cnf_transformation,[],[f24])).
% 7.38/1.44  
% 7.38/1.44  fof(f65,plain,(
% 7.38/1.44    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.38/1.44    inference(equality_resolution,[],[f40])).
% 7.38/1.44  
% 7.38/1.44  fof(f58,plain,(
% 7.38/1.44    ( ! [X0,X3,X1] : (sP0(X0,X1) | ~r2_hidden(sK2(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1),X0)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f31])).
% 7.38/1.44  
% 7.38/1.44  fof(f4,axiom,(
% 7.38/1.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.38/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.38/1.44  
% 7.38/1.44  fof(f10,plain,(
% 7.38/1.44    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.38/1.44    inference(ennf_transformation,[],[f4])).
% 7.38/1.44  
% 7.38/1.44  fof(f45,plain,(
% 7.38/1.44    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f10])).
% 7.38/1.44  
% 7.38/1.44  fof(f39,plain,(
% 7.38/1.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f22])).
% 7.38/1.44  
% 7.38/1.44  fof(f3,axiom,(
% 7.38/1.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.38/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.38/1.44  
% 7.38/1.44  fof(f25,plain,(
% 7.38/1.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.38/1.44    inference(nnf_transformation,[],[f3])).
% 7.38/1.44  
% 7.38/1.44  fof(f44,plain,(
% 7.38/1.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f25])).
% 7.38/1.44  
% 7.38/1.44  fof(f5,axiom,(
% 7.38/1.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 7.38/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.38/1.44  
% 7.38/1.44  fof(f11,plain,(
% 7.38/1.44    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.38/1.44    inference(ennf_transformation,[],[f5])).
% 7.38/1.44  
% 7.38/1.44  fof(f12,plain,(
% 7.38/1.44    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.38/1.44    inference(flattening,[],[f11])).
% 7.38/1.44  
% 7.38/1.44  fof(f46,plain,(
% 7.38/1.44    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f12])).
% 7.38/1.44  
% 7.38/1.44  fof(f42,plain,(
% 7.38/1.44    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f24])).
% 7.38/1.44  
% 7.38/1.44  fof(f43,plain,(
% 7.38/1.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.38/1.44    inference(cnf_transformation,[],[f25])).
% 7.38/1.44  
% 7.38/1.44  fof(f54,plain,(
% 7.38/1.44    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1),X0)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f31])).
% 7.38/1.44  
% 7.38/1.44  fof(f55,plain,(
% 7.38/1.44    ( ! [X0,X1] : (sP0(X0,X1) | v3_pre_topc(sK3(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f31])).
% 7.38/1.44  
% 7.38/1.44  fof(f51,plain,(
% 7.38/1.44    ( ! [X0,X5,X1] : (r1_tarski(sK4(X0,X1,X5),X0) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f31])).
% 7.38/1.44  
% 7.38/1.44  fof(f52,plain,(
% 7.38/1.44    ( ! [X0,X5,X1] : (r2_hidden(X5,sK4(X0,X1,X5)) | ~r2_hidden(X5,X0) | ~sP0(X0,X1)) )),
% 7.38/1.44    inference(cnf_transformation,[],[f31])).
% 7.38/1.44  
% 7.38/1.44  cnf(c_2,plain,
% 7.38/1.44      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.38/1.44      inference(cnf_transformation,[],[f37]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_7572,plain,
% 7.38/1.44      ( r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),X0)
% 7.38/1.44      | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK4(sK6,X1,sK1(sK6,k1_tops_1(sK5,sK6))))
% 7.38/1.44      | ~ r1_tarski(sK4(sK6,X1,sK1(sK6,k1_tops_1(sK5,sK6))),X0) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_2]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_16092,plain,
% 7.38/1.44      ( ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK4(sK6,X0,sK1(sK6,k1_tops_1(sK5,sK6))))
% 7.38/1.44      | r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),k1_tops_1(sK5,sK6))
% 7.38/1.44      | ~ r1_tarski(sK4(sK6,X0,sK1(sK6,k1_tops_1(sK5,sK6))),k1_tops_1(sK5,sK6)) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_7572]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_16094,plain,
% 7.38/1.44      ( ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))))
% 7.38/1.44      | r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),k1_tops_1(sK5,sK6))
% 7.38/1.44      | ~ r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),k1_tops_1(sK5,sK6)) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_16092]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_1,plain,
% 7.38/1.44      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.38/1.44      inference(cnf_transformation,[],[f38]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3164,plain,
% 7.38/1.44      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 7.38/1.44      | r1_tarski(X0,X1) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_23,negated_conjecture,
% 7.38/1.44      ( sP0(sK6,sK5) | v3_pre_topc(sK6,sK5) ),
% 7.38/1.44      inference(cnf_transformation,[],[f62]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3147,plain,
% 7.38/1.44      ( sP0(sK6,sK5) = iProver_top | v3_pre_topc(sK6,sK5) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_20,plain,
% 7.38/1.44      ( ~ sP0(X0,X1)
% 7.38/1.44      | v3_pre_topc(sK4(X0,X1,X2),X1)
% 7.38/1.44      | ~ r2_hidden(X2,X0) ),
% 7.38/1.44      inference(cnf_transformation,[],[f50]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3150,plain,
% 7.38/1.44      ( sP0(X0,X1) != iProver_top
% 7.38/1.44      | v3_pre_topc(sK4(X0,X1,X2),X1) = iProver_top
% 7.38/1.44      | r2_hidden(X2,X0) != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_21,plain,
% 7.38/1.44      ( ~ sP0(X0,X1)
% 7.38/1.44      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ r2_hidden(X2,X0) ),
% 7.38/1.44      inference(cnf_transformation,[],[f49]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3149,plain,
% 7.38/1.44      ( sP0(X0,X1) != iProver_top
% 7.38/1.44      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.38/1.44      | r2_hidden(X2,X0) != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_11,plain,
% 7.38/1.44      ( ~ v3_pre_topc(X0,X1)
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ v2_pre_topc(X3)
% 7.38/1.44      | ~ l1_pre_topc(X3)
% 7.38/1.44      | ~ l1_pre_topc(X1)
% 7.38/1.44      | k1_tops_1(X1,X0) = X0 ),
% 7.38/1.44      inference(cnf_transformation,[],[f47]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_26,negated_conjecture,
% 7.38/1.44      ( v2_pre_topc(sK5) ),
% 7.38/1.44      inference(cnf_transformation,[],[f59]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_379,plain,
% 7.38/1.44      ( ~ v3_pre_topc(X0,X1)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.38/1.44      | ~ l1_pre_topc(X1)
% 7.38/1.44      | ~ l1_pre_topc(X3)
% 7.38/1.44      | k1_tops_1(X1,X0) = X0
% 7.38/1.44      | sK5 != X3 ),
% 7.38/1.44      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_380,plain,
% 7.38/1.44      ( ~ v3_pre_topc(X0,X1)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ l1_pre_topc(X1)
% 7.38/1.44      | ~ l1_pre_topc(sK5)
% 7.38/1.44      | k1_tops_1(X1,X0) = X0 ),
% 7.38/1.44      inference(unflattening,[status(thm)],[c_379]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_25,negated_conjecture,
% 7.38/1.44      ( l1_pre_topc(sK5) ),
% 7.38/1.44      inference(cnf_transformation,[],[f60]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_384,plain,
% 7.38/1.44      ( ~ l1_pre_topc(X1)
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ v3_pre_topc(X0,X1)
% 7.38/1.44      | k1_tops_1(X1,X0) = X0 ),
% 7.38/1.44      inference(global_propositional_subsumption,
% 7.38/1.44                [status(thm)],
% 7.38/1.44                [c_380,c_25]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_385,plain,
% 7.38/1.44      ( ~ v3_pre_topc(X0,X1)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ l1_pre_topc(X1)
% 7.38/1.44      | k1_tops_1(X1,X0) = X0 ),
% 7.38/1.44      inference(renaming,[status(thm)],[c_384]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_416,plain,
% 7.38/1.44      ( ~ v3_pre_topc(X0,X1)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | k1_tops_1(X1,X0) = X0
% 7.38/1.44      | sK5 != X1 ),
% 7.38/1.44      inference(resolution_lifted,[status(thm)],[c_385,c_25]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_417,plain,
% 7.38/1.44      ( ~ v3_pre_topc(X0,sK5)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | k1_tops_1(sK5,X0) = X0 ),
% 7.38/1.44      inference(unflattening,[status(thm)],[c_416]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_2517,plain,
% 7.38/1.44      ( ~ v3_pre_topc(X0,sK5)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | k1_tops_1(sK5,X0) = X0
% 7.38/1.44      | ~ sP2_iProver_split ),
% 7.38/1.44      inference(splitting,
% 7.38/1.44                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 7.38/1.44                [c_417]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3144,plain,
% 7.38/1.44      ( k1_tops_1(sK5,X0) = X0
% 7.38/1.44      | v3_pre_topc(X0,sK5) != iProver_top
% 7.38/1.44      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | sP2_iProver_split != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_2517]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_2518,plain,
% 7.38/1.44      ( sP2_iProver_split | sP0_iProver_split ),
% 7.38/1.44      inference(splitting,
% 7.38/1.44                [splitting(split),new_symbols(definition,[])],
% 7.38/1.44                [c_417]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_2547,plain,
% 7.38/1.44      ( sP2_iProver_split = iProver_top
% 7.38/1.44      | sP0_iProver_split = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_2518]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_2548,plain,
% 7.38/1.44      ( k1_tops_1(sK5,X0) = X0
% 7.38/1.44      | v3_pre_topc(X0,sK5) != iProver_top
% 7.38/1.44      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | sP2_iProver_split != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_2517]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_24,negated_conjecture,
% 7.38/1.44      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.38/1.44      inference(cnf_transformation,[],[f61]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3146,plain,
% 7.38/1.44      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_10,plain,
% 7.38/1.44      ( v3_pre_topc(X0,X1)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.38/1.44      | ~ v2_pre_topc(X1)
% 7.38/1.44      | ~ l1_pre_topc(X1)
% 7.38/1.44      | ~ l1_pre_topc(X3)
% 7.38/1.44      | k1_tops_1(X1,X0) != X0 ),
% 7.38/1.44      inference(cnf_transformation,[],[f48]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_354,plain,
% 7.38/1.44      ( v3_pre_topc(X0,X1)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.38/1.44      | ~ l1_pre_topc(X1)
% 7.38/1.44      | ~ l1_pre_topc(X3)
% 7.38/1.44      | k1_tops_1(X1,X0) != X0
% 7.38/1.44      | sK5 != X1 ),
% 7.38/1.44      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_355,plain,
% 7.38/1.44      ( v3_pre_topc(X0,sK5)
% 7.38/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ l1_pre_topc(X2)
% 7.38/1.44      | ~ l1_pre_topc(sK5)
% 7.38/1.44      | k1_tops_1(sK5,X0) != X0 ),
% 7.38/1.44      inference(unflattening,[status(thm)],[c_354]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_359,plain,
% 7.38/1.44      ( ~ l1_pre_topc(X2)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.38/1.44      | v3_pre_topc(X0,sK5)
% 7.38/1.44      | k1_tops_1(sK5,X0) != X0 ),
% 7.38/1.44      inference(global_propositional_subsumption,
% 7.38/1.44                [status(thm)],
% 7.38/1.44                [c_355,c_25]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_360,plain,
% 7.38/1.44      ( v3_pre_topc(X0,sK5)
% 7.38/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ l1_pre_topc(X2)
% 7.38/1.44      | k1_tops_1(sK5,X0) != X0 ),
% 7.38/1.44      inference(renaming,[status(thm)],[c_359]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_464,plain,
% 7.38/1.44      ( v3_pre_topc(X0,sK5)
% 7.38/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | k1_tops_1(sK5,X0) != X0
% 7.38/1.44      | sK5 != X2 ),
% 7.38/1.44      inference(resolution_lifted,[status(thm)],[c_25,c_360]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_465,plain,
% 7.38/1.44      ( v3_pre_topc(X0,sK5)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | k1_tops_1(sK5,X0) != X0 ),
% 7.38/1.44      inference(unflattening,[status(thm)],[c_464]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_2514,plain,
% 7.38/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ sP0_iProver_split ),
% 7.38/1.44      inference(splitting,
% 7.38/1.44                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.38/1.44                [c_465]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3140,plain,
% 7.38/1.44      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | sP0_iProver_split != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_2514]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3396,plain,
% 7.38/1.44      ( sP0_iProver_split != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3146,c_3140]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3753,plain,
% 7.38/1.44      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | v3_pre_topc(X0,sK5) != iProver_top
% 7.38/1.44      | k1_tops_1(sK5,X0) = X0 ),
% 7.38/1.44      inference(global_propositional_subsumption,
% 7.38/1.44                [status(thm)],
% 7.38/1.44                [c_3144,c_2547,c_2548,c_3396]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3754,plain,
% 7.38/1.44      ( k1_tops_1(sK5,X0) = X0
% 7.38/1.44      | v3_pre_topc(X0,sK5) != iProver_top
% 7.38/1.44      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 7.38/1.44      inference(renaming,[status(thm)],[c_3753]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4197,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK4(X0,sK5,X1)) = sK4(X0,sK5,X1)
% 7.38/1.44      | sP0(X0,sK5) != iProver_top
% 7.38/1.44      | v3_pre_topc(sK4(X0,sK5,X1),sK5) != iProver_top
% 7.38/1.44      | r2_hidden(X1,X0) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3149,c_3754]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4837,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK4(X0,sK5,X1)) = sK4(X0,sK5,X1)
% 7.38/1.44      | sP0(X0,sK5) != iProver_top
% 7.38/1.44      | r2_hidden(X1,X0) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3150,c_4197]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5495,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK4(sK6,sK5,X0)) = sK4(sK6,sK5,X0)
% 7.38/1.44      | v3_pre_topc(sK6,sK5) = iProver_top
% 7.38/1.44      | r2_hidden(X0,sK6) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3147,c_4837]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_29,plain,
% 7.38/1.44      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_22,negated_conjecture,
% 7.38/1.44      ( ~ sP0(sK6,sK5) | ~ v3_pre_topc(sK6,sK5) ),
% 7.38/1.44      inference(cnf_transformation,[],[f63]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_31,plain,
% 7.38/1.44      ( sP0(sK6,sK5) != iProver_top
% 7.38/1.44      | v3_pre_topc(sK6,sK5) != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_14,plain,
% 7.38/1.44      ( sP0(X0,X1)
% 7.38/1.44      | r2_hidden(sK2(X0,X1),X0)
% 7.38/1.44      | r1_tarski(sK3(X0,X1),X0) ),
% 7.38/1.44      inference(cnf_transformation,[],[f56]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_205,plain,
% 7.38/1.44      ( ~ sP0(sK6,sK5) | ~ v3_pre_topc(sK6,sK5) ),
% 7.38/1.44      inference(prop_impl,[status(thm)],[c_22]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_1207,plain,
% 7.38/1.44      ( ~ v3_pre_topc(sK6,sK5)
% 7.38/1.44      | r2_hidden(sK2(X0,X1),X0)
% 7.38/1.44      | r1_tarski(sK3(X0,X1),X0)
% 7.38/1.44      | sK5 != X1
% 7.38/1.44      | sK6 != X0 ),
% 7.38/1.44      inference(resolution_lifted,[status(thm)],[c_14,c_205]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_1208,plain,
% 7.38/1.44      ( ~ v3_pre_topc(sK6,sK5)
% 7.38/1.44      | r2_hidden(sK2(sK6,sK5),sK6)
% 7.38/1.44      | r1_tarski(sK3(sK6,sK5),sK6) ),
% 7.38/1.44      inference(unflattening,[status(thm)],[c_1207]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_1209,plain,
% 7.38/1.44      ( v3_pre_topc(sK6,sK5) != iProver_top
% 7.38/1.44      | r2_hidden(sK2(sK6,sK5),sK6) = iProver_top
% 7.38/1.44      | r1_tarski(sK3(sK6,sK5),sK6) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_13,plain,
% 7.38/1.44      ( sP0(X0,X1)
% 7.38/1.44      | r2_hidden(sK2(X0,X1),X0)
% 7.38/1.44      | r2_hidden(sK2(X0,X1),sK3(X0,X1)) ),
% 7.38/1.44      inference(cnf_transformation,[],[f57]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_1220,plain,
% 7.38/1.44      ( ~ v3_pre_topc(sK6,sK5)
% 7.38/1.44      | r2_hidden(sK2(X0,X1),X0)
% 7.38/1.44      | r2_hidden(sK2(X0,X1),sK3(X0,X1))
% 7.38/1.44      | sK5 != X1
% 7.38/1.44      | sK6 != X0 ),
% 7.38/1.44      inference(resolution_lifted,[status(thm)],[c_13,c_205]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_1221,plain,
% 7.38/1.44      ( ~ v3_pre_topc(sK6,sK5)
% 7.38/1.44      | r2_hidden(sK2(sK6,sK5),sK3(sK6,sK5))
% 7.38/1.44      | r2_hidden(sK2(sK6,sK5),sK6) ),
% 7.38/1.44      inference(unflattening,[status(thm)],[c_1220]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_1222,plain,
% 7.38/1.44      ( v3_pre_topc(sK6,sK5) != iProver_top
% 7.38/1.44      | r2_hidden(sK2(sK6,sK5),sK3(sK6,sK5)) = iProver_top
% 7.38/1.44      | r2_hidden(sK2(sK6,sK5),sK6) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_1221]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5,plain,
% 7.38/1.44      ( r1_tarski(X0,X0) ),
% 7.38/1.44      inference(cnf_transformation,[],[f65]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3666,plain,
% 7.38/1.44      ( r1_tarski(sK6,sK6) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_5]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3669,plain,
% 7.38/1.44      ( r1_tarski(sK6,sK6) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_3666]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4071,plain,
% 7.38/1.44      ( r2_hidden(sK2(sK6,sK5),X0)
% 7.38/1.44      | ~ r2_hidden(sK2(sK6,sK5),sK3(sK6,sK5))
% 7.38/1.44      | ~ r1_tarski(sK3(sK6,sK5),X0) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_2]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5148,plain,
% 7.38/1.44      ( ~ r2_hidden(sK2(sK6,sK5),sK3(sK6,sK5))
% 7.38/1.44      | r2_hidden(sK2(sK6,sK5),sK6)
% 7.38/1.44      | ~ r1_tarski(sK3(sK6,sK5),sK6) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_4071]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5149,plain,
% 7.38/1.44      ( r2_hidden(sK2(sK6,sK5),sK3(sK6,sK5)) != iProver_top
% 7.38/1.44      | r2_hidden(sK2(sK6,sK5),sK6) = iProver_top
% 7.38/1.44      | r1_tarski(sK3(sK6,sK5),sK6) != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_5148]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_12,plain,
% 7.38/1.44      ( sP0(X0,X1)
% 7.38/1.44      | ~ v3_pre_topc(X2,X1)
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ r2_hidden(sK2(X0,X1),X2)
% 7.38/1.44      | ~ r2_hidden(sK2(X0,X1),X0)
% 7.38/1.44      | ~ r1_tarski(X2,X0) ),
% 7.38/1.44      inference(cnf_transformation,[],[f58]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5046,plain,
% 7.38/1.44      ( sP0(X0,sK5)
% 7.38/1.44      | ~ v3_pre_topc(sK6,sK5)
% 7.38/1.44      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ r2_hidden(sK2(X0,sK5),X0)
% 7.38/1.44      | ~ r2_hidden(sK2(X0,sK5),sK6)
% 7.38/1.44      | ~ r1_tarski(sK6,X0) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_12]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5217,plain,
% 7.38/1.44      ( sP0(sK6,sK5)
% 7.38/1.44      | ~ v3_pre_topc(sK6,sK5)
% 7.38/1.44      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ r2_hidden(sK2(sK6,sK5),sK6)
% 7.38/1.44      | ~ r1_tarski(sK6,sK6) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_5046]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5218,plain,
% 7.38/1.44      ( sP0(sK6,sK5) = iProver_top
% 7.38/1.44      | v3_pre_topc(sK6,sK5) != iProver_top
% 7.38/1.44      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | r2_hidden(sK2(sK6,sK5),sK6) != iProver_top
% 7.38/1.44      | r1_tarski(sK6,sK6) != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_5217]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5830,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK4(sK6,sK5,X0)) = sK4(sK6,sK5,X0)
% 7.38/1.44      | r2_hidden(X0,sK6) != iProver_top ),
% 7.38/1.44      inference(global_propositional_subsumption,
% 7.38/1.44                [status(thm)],
% 7.38/1.44                [c_5495,c_29,c_31,c_1209,c_1222,c_3669,c_5149,c_5218]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5838,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK4(sK6,sK5,sK1(sK6,X0))) = sK4(sK6,sK5,sK1(sK6,X0))
% 7.38/1.44      | r1_tarski(sK6,X0) = iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3164,c_5830]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_8,plain,
% 7.38/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.38/1.44      | ~ l1_pre_topc(X1) ),
% 7.38/1.44      inference(cnf_transformation,[],[f45]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_452,plain,
% 7.38/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.38/1.44      | sK5 != X1 ),
% 7.38/1.44      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_453,plain,
% 7.38/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X0),X0) ),
% 7.38/1.44      inference(unflattening,[status(thm)],[c_452]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3141,plain,
% 7.38/1.44      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X0),X0) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3403,plain,
% 7.38/1.44      ( r1_tarski(k1_tops_1(sK5,sK6),sK6) = iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3146,c_3141]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3163,plain,
% 7.38/1.44      ( r2_hidden(X0,X1) != iProver_top
% 7.38/1.44      | r2_hidden(X0,X2) = iProver_top
% 7.38/1.44      | r1_tarski(X1,X2) != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4334,plain,
% 7.38/1.44      ( r2_hidden(sK1(X0,X1),X2) = iProver_top
% 7.38/1.44      | r1_tarski(X0,X2) != iProver_top
% 7.38/1.44      | r1_tarski(X0,X1) = iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3164,c_3163]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5566,plain,
% 7.38/1.44      ( r2_hidden(sK1(X0,X1),X2) = iProver_top
% 7.38/1.44      | r1_tarski(X0,X3) != iProver_top
% 7.38/1.44      | r1_tarski(X3,X2) != iProver_top
% 7.38/1.44      | r1_tarski(X0,X1) = iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_4334,c_3163]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_6715,plain,
% 7.38/1.44      ( r2_hidden(sK1(k1_tops_1(sK5,sK6),X0),X1) = iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,sK6),X0) = iProver_top
% 7.38/1.44      | r1_tarski(sK6,X1) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3403,c_5566]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_0,plain,
% 7.38/1.44      ( ~ r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.38/1.44      inference(cnf_transformation,[],[f39]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3165,plain,
% 7.38/1.44      ( r2_hidden(sK1(X0,X1),X1) != iProver_top
% 7.38/1.44      | r1_tarski(X0,X1) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_6965,plain,
% 7.38/1.44      ( r1_tarski(k1_tops_1(sK5,sK6),X0) = iProver_top
% 7.38/1.44      | r1_tarski(sK6,X0) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_6715,c_3165]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_6,plain,
% 7.38/1.44      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.38/1.44      inference(cnf_transformation,[],[f44]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3160,plain,
% 7.38/1.44      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.38/1.44      | r1_tarski(X0,X1) != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_9,plain,
% 7.38/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ r1_tarski(X0,X2)
% 7.38/1.44      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.38/1.44      | ~ l1_pre_topc(X1) ),
% 7.38/1.44      inference(cnf_transformation,[],[f46]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_434,plain,
% 7.38/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | ~ r1_tarski(X0,X2)
% 7.38/1.44      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.38/1.44      | sK5 != X1 ),
% 7.38/1.44      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_435,plain,
% 7.38/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ r1_tarski(X0,X1)
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X0),k1_tops_1(sK5,X1)) ),
% 7.38/1.44      inference(unflattening,[status(thm)],[c_434]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3142,plain,
% 7.38/1.44      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | r1_tarski(X0,X1) != iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X0),k1_tops_1(sK5,X1)) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3,plain,
% 7.38/1.44      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.38/1.44      inference(cnf_transformation,[],[f42]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3162,plain,
% 7.38/1.44      ( X0 = X1
% 7.38/1.44      | r1_tarski(X1,X0) != iProver_top
% 7.38/1.44      | r1_tarski(X0,X1) != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4297,plain,
% 7.38/1.44      ( k1_tops_1(sK5,X0) = k1_tops_1(sK5,X1)
% 7.38/1.44      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | r1_tarski(X1,X0) != iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X0),k1_tops_1(sK5,X1)) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3142,c_3162]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4592,plain,
% 7.38/1.44      ( k1_tops_1(sK5,X0) = k1_tops_1(sK5,X1)
% 7.38/1.44      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | r1_tarski(X1,X0) != iProver_top
% 7.38/1.44      | r1_tarski(X0,X1) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3142,c_4297]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4694,plain,
% 7.38/1.44      ( k1_tops_1(sK5,X0) = k1_tops_1(sK5,sK6)
% 7.38/1.44      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | r1_tarski(X0,sK6) != iProver_top
% 7.38/1.44      | r1_tarski(sK6,X0) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3146,c_4592]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4737,plain,
% 7.38/1.44      ( k1_tops_1(sK5,X0) = k1_tops_1(sK5,sK6)
% 7.38/1.44      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
% 7.38/1.44      | r1_tarski(X0,sK6) != iProver_top
% 7.38/1.44      | r1_tarski(sK6,X0) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3160,c_4694]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_7487,plain,
% 7.38/1.44      ( k1_tops_1(sK5,k1_tops_1(sK5,sK6)) = k1_tops_1(sK5,sK6)
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,sK6),sK6) != iProver_top
% 7.38/1.44      | r1_tarski(sK6,k1_tops_1(sK5,sK6)) != iProver_top
% 7.38/1.44      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_6965,c_4737]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3361,plain,
% 7.38/1.44      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,sK6),sK6) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_453]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3362,plain,
% 7.38/1.44      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,sK6),sK6) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_3361]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_2515,plain,
% 7.38/1.44      ( v3_pre_topc(X0,sK5)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | k1_tops_1(sK5,X0) != X0
% 7.38/1.44      | ~ sP1_iProver_split ),
% 7.38/1.44      inference(splitting,
% 7.38/1.44                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.38/1.44                [c_465]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_2516,plain,
% 7.38/1.44      ( sP1_iProver_split | sP0_iProver_split ),
% 7.38/1.44      inference(splitting,
% 7.38/1.44                [splitting(split),new_symbols(definition,[])],
% 7.38/1.44                [c_465]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_2610,plain,
% 7.38/1.44      ( k1_tops_1(sK5,X0) != X0
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | v3_pre_topc(X0,sK5) ),
% 7.38/1.44      inference(global_propositional_subsumption,
% 7.38/1.44                [status(thm)],
% 7.38/1.44                [c_2515,c_2516,c_2514]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_2611,plain,
% 7.38/1.44      ( v3_pre_topc(X0,sK5)
% 7.38/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | k1_tops_1(sK5,X0) != X0 ),
% 7.38/1.44      inference(renaming,[status(thm)],[c_2610]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3364,plain,
% 7.38/1.44      ( v3_pre_topc(sK6,sK5)
% 7.38/1.44      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | k1_tops_1(sK5,sK6) != sK6 ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_2611]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3365,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK6) != sK6
% 7.38/1.44      | v3_pre_topc(sK6,sK5) = iProver_top
% 7.38/1.44      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_3364]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3405,plain,
% 7.38/1.44      ( ~ r1_tarski(k1_tops_1(sK5,sK6),sK6)
% 7.38/1.44      | ~ r1_tarski(sK6,k1_tops_1(sK5,sK6))
% 7.38/1.44      | k1_tops_1(sK5,sK6) = sK6 ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_3]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3406,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK6) = sK6
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,sK6),sK6) != iProver_top
% 7.38/1.44      | r1_tarski(sK6,k1_tops_1(sK5,sK6)) != iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_3405]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_9762,plain,
% 7.38/1.44      ( r1_tarski(sK6,k1_tops_1(sK5,sK6)) != iProver_top ),
% 7.38/1.44      inference(global_propositional_subsumption,
% 7.38/1.44                [status(thm)],
% 7.38/1.44                [c_7487,c_29,c_31,c_1209,c_1222,c_3362,c_3365,c_3406,
% 7.38/1.44                 c_3669,c_5149,c_5218]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_9767,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6)))) = sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))) ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_5838,c_9762]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3161,plain,
% 7.38/1.44      ( r1_tarski(X0,X0) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_6712,plain,
% 7.38/1.44      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | r2_hidden(sK1(k1_tops_1(sK5,X0),X2),X3) = iProver_top
% 7.38/1.44      | r1_tarski(X0,X1) != iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X1),X3) != iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X0),X2) = iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3142,c_5566]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_7048,plain,
% 7.38/1.44      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | r2_hidden(sK1(k1_tops_1(sK5,X0),X1),X2) = iProver_top
% 7.38/1.44      | r1_tarski(X0,sK6) != iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X0),X1) = iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,sK6),X2) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3146,c_6712]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_7141,plain,
% 7.38/1.44      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.38/1.44      | r1_tarski(X0,sK6) != iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X0),X1) = iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,sK6),X1) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_7048,c_3165]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_7184,plain,
% 7.38/1.44      ( r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
% 7.38/1.44      | r1_tarski(X0,sK6) != iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X0),X1) = iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,sK6),X1) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3160,c_7141]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_8734,plain,
% 7.38/1.44      ( r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
% 7.38/1.44      | r1_tarski(X0,sK6) != iProver_top
% 7.38/1.44      | r1_tarski(k1_tops_1(sK5,X0),k1_tops_1(sK5,sK6)) = iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3161,c_7184]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_9772,plain,
% 7.38/1.44      ( r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),k1_tops_1(sK5,sK6)) = iProver_top
% 7.38/1.44      | r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),u1_struct_0(sK5)) != iProver_top
% 7.38/1.44      | r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),sK6) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_9767,c_8734]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_9882,plain,
% 7.38/1.44      ( r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),k1_tops_1(sK5,sK6))
% 7.38/1.44      | ~ r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),u1_struct_0(sK5))
% 7.38/1.44      | ~ r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),sK6) ),
% 7.38/1.44      inference(predicate_to_equality_rev,[status(thm)],[c_9772]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_7,plain,
% 7.38/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.38/1.44      inference(cnf_transformation,[],[f43]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3412,plain,
% 7.38/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | r1_tarski(X0,u1_struct_0(sK5)) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_7]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_7874,plain,
% 7.38/1.44      ( ~ m1_subset_1(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),u1_struct_0(sK5)) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_3412]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_16,plain,
% 7.38/1.44      ( sP0(X0,X1)
% 7.38/1.44      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
% 7.38/1.44      | r2_hidden(sK2(X0,X1),X0) ),
% 7.38/1.44      inference(cnf_transformation,[],[f54]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3154,plain,
% 7.38/1.44      ( sP0(X0,X1) = iProver_top
% 7.38/1.44      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.38/1.44      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4975,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK3(X0,sK5)) = sK3(X0,sK5)
% 7.38/1.44      | sP0(X0,sK5) = iProver_top
% 7.38/1.44      | v3_pre_topc(sK3(X0,sK5),sK5) != iProver_top
% 7.38/1.44      | r2_hidden(sK2(X0,sK5),X0) = iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3154,c_3754]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_15,plain,
% 7.38/1.44      ( sP0(X0,X1)
% 7.38/1.44      | v3_pre_topc(sK3(X0,X1),X1)
% 7.38/1.44      | r2_hidden(sK2(X0,X1),X0) ),
% 7.38/1.44      inference(cnf_transformation,[],[f55]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3155,plain,
% 7.38/1.44      ( sP0(X0,X1) = iProver_top
% 7.38/1.44      | v3_pre_topc(sK3(X0,X1),X1) = iProver_top
% 7.38/1.44      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5197,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK3(X0,sK5)) = sK3(X0,sK5)
% 7.38/1.44      | sP0(X0,sK5) = iProver_top
% 7.38/1.44      | r2_hidden(sK2(X0,sK5),X0) = iProver_top ),
% 7.38/1.44      inference(forward_subsumption_resolution,
% 7.38/1.44                [status(thm)],
% 7.38/1.44                [c_4975,c_3155]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_5843,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK4(sK6,sK5,sK2(sK6,sK5))) = sK4(sK6,sK5,sK2(sK6,sK5))
% 7.38/1.44      | k1_tops_1(sK5,sK3(sK6,sK5)) = sK3(sK6,sK5)
% 7.38/1.44      | sP0(sK6,sK5) = iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_5197,c_5830]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_30,plain,
% 7.38/1.44      ( sP0(sK6,sK5) = iProver_top | v3_pre_topc(sK6,sK5) = iProver_top ),
% 7.38/1.44      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_6375,plain,
% 7.38/1.44      ( sP0(sK6,sK5) = iProver_top ),
% 7.38/1.44      inference(global_propositional_subsumption,
% 7.38/1.44                [status(thm)],
% 7.38/1.44                [c_5843,c_29,c_30,c_31,c_1209,c_1222,c_3669,c_5149,
% 7.38/1.44                 c_5218]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4358,plain,
% 7.38/1.44      ( ~ sP0(sK6,X0)
% 7.38/1.44      | m1_subset_1(sK4(sK6,X0,sK1(sK6,k1_tops_1(sK5,sK6))),k1_zfmisc_1(u1_struct_0(X0)))
% 7.38/1.44      | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_21]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4375,plain,
% 7.38/1.44      ( ~ sP0(sK6,sK5)
% 7.38/1.44      | m1_subset_1(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.38/1.44      | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_4358]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_19,plain,
% 7.38/1.44      ( ~ sP0(X0,X1) | ~ r2_hidden(X2,X0) | r1_tarski(sK4(X0,X1,X2),X0) ),
% 7.38/1.44      inference(cnf_transformation,[],[f51]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4360,plain,
% 7.38/1.44      ( ~ sP0(sK6,X0)
% 7.38/1.44      | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6)
% 7.38/1.44      | r1_tarski(sK4(sK6,X0,sK1(sK6,k1_tops_1(sK5,sK6))),sK6) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_19]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4367,plain,
% 7.38/1.44      ( ~ sP0(sK6,sK5)
% 7.38/1.44      | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6)
% 7.38/1.44      | r1_tarski(sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))),sK6) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_4360]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_18,plain,
% 7.38/1.44      ( ~ sP0(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,sK4(X0,X1,X2)) ),
% 7.38/1.44      inference(cnf_transformation,[],[f52]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4361,plain,
% 7.38/1.44      ( ~ sP0(sK6,X0)
% 7.38/1.44      | r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK4(sK6,X0,sK1(sK6,k1_tops_1(sK5,sK6))))
% 7.38/1.44      | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_18]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_4363,plain,
% 7.38/1.44      ( ~ sP0(sK6,sK5)
% 7.38/1.44      | r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK4(sK6,sK5,sK1(sK6,k1_tops_1(sK5,sK6))))
% 7.38/1.44      | ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_4361]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3761,plain,
% 7.38/1.44      ( k1_tops_1(sK5,sK6) = sK6 | v3_pre_topc(sK6,sK5) != iProver_top ),
% 7.38/1.44      inference(superposition,[status(thm)],[c_3146,c_3754]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3775,plain,
% 7.38/1.44      ( ~ v3_pre_topc(sK6,sK5) | k1_tops_1(sK5,sK6) = sK6 ),
% 7.38/1.44      inference(predicate_to_equality_rev,[status(thm)],[c_3761]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3461,plain,
% 7.38/1.44      ( ~ r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),k1_tops_1(sK5,sK6))
% 7.38/1.44      | r1_tarski(sK6,k1_tops_1(sK5,sK6)) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_0]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(c_3462,plain,
% 7.38/1.44      ( r2_hidden(sK1(sK6,k1_tops_1(sK5,sK6)),sK6)
% 7.38/1.44      | r1_tarski(sK6,k1_tops_1(sK5,sK6)) ),
% 7.38/1.44      inference(instantiation,[status(thm)],[c_1]) ).
% 7.38/1.44  
% 7.38/1.44  cnf(contradiction,plain,
% 7.38/1.44      ( $false ),
% 7.38/1.44      inference(minisat,
% 7.38/1.44                [status(thm)],
% 7.38/1.44                [c_16094,c_9882,c_7874,c_6375,c_4375,c_4367,c_4363,
% 7.38/1.44                 c_3775,c_3461,c_3462,c_3405,c_3365,c_3361,c_31,c_23,
% 7.38/1.44                 c_29,c_24]) ).
% 7.38/1.44  
% 7.38/1.44  
% 7.38/1.44  % SZS output end CNFRefutation for theBenchmark.p
% 7.38/1.44  
% 7.38/1.44  ------                               Statistics
% 7.38/1.44  
% 7.38/1.44  ------ General
% 7.38/1.44  
% 7.38/1.44  abstr_ref_over_cycles:                  0
% 7.38/1.44  abstr_ref_under_cycles:                 0
% 7.38/1.44  gc_basic_clause_elim:                   0
% 7.38/1.44  forced_gc_time:                         0
% 7.38/1.44  parsing_time:                           0.008
% 7.38/1.44  unif_index_cands_time:                  0.
% 7.38/1.44  unif_index_add_time:                    0.
% 7.38/1.44  orderings_time:                         0.
% 7.38/1.44  out_proof_time:                         0.012
% 7.38/1.44  total_time:                             0.507
% 7.38/1.44  num_of_symbols:                         50
% 7.38/1.44  num_of_terms:                           8979
% 7.38/1.44  
% 7.38/1.44  ------ Preprocessing
% 7.38/1.44  
% 7.38/1.44  num_of_splits:                          4
% 7.38/1.44  num_of_split_atoms:                     3
% 7.38/1.44  num_of_reused_defs:                     1
% 7.38/1.44  num_eq_ax_congr_red:                    31
% 7.38/1.44  num_of_sem_filtered_clauses:            4
% 7.38/1.44  num_of_subtypes:                        0
% 7.38/1.44  monotx_restored_types:                  0
% 7.38/1.44  sat_num_of_epr_types:                   0
% 7.38/1.44  sat_num_of_non_cyclic_types:            0
% 7.38/1.44  sat_guarded_non_collapsed_types:        0
% 7.38/1.44  num_pure_diseq_elim:                    0
% 7.38/1.44  simp_replaced_by:                       0
% 7.38/1.44  res_preprocessed:                       122
% 7.38/1.44  prep_upred:                             0
% 7.38/1.44  prep_unflattend:                        94
% 7.38/1.44  smt_new_axioms:                         0
% 7.38/1.44  pred_elim_cands:                        5
% 7.38/1.44  pred_elim:                              2
% 7.38/1.44  pred_elim_cl:                           2
% 7.38/1.44  pred_elim_cycles:                       6
% 7.38/1.44  merged_defs:                            16
% 7.38/1.44  merged_defs_ncl:                        0
% 7.38/1.44  bin_hyper_res:                          16
% 7.38/1.44  prep_cycles:                            4
% 7.38/1.44  pred_elim_time:                         0.049
% 7.38/1.44  splitting_time:                         0.
% 7.38/1.44  sem_filter_time:                        0.
% 7.38/1.44  monotx_time:                            0.001
% 7.38/1.44  subtype_inf_time:                       0.
% 7.38/1.44  
% 7.38/1.44  ------ Problem properties
% 7.38/1.44  
% 7.38/1.44  clauses:                                28
% 7.38/1.44  conjectures:                            3
% 7.38/1.44  epr:                                    7
% 7.38/1.44  horn:                                   20
% 7.38/1.44  ground:                                 5
% 7.38/1.44  unary:                                  2
% 7.38/1.44  binary:                                 11
% 7.38/1.44  lits:                                   78
% 7.38/1.44  lits_eq:                                3
% 7.38/1.44  fd_pure:                                0
% 7.38/1.44  fd_pseudo:                              0
% 7.38/1.44  fd_cond:                                0
% 7.38/1.44  fd_pseudo_cond:                         1
% 7.38/1.44  ac_symbols:                             0
% 7.38/1.44  
% 7.38/1.44  ------ Propositional Solver
% 7.38/1.44  
% 7.38/1.44  prop_solver_calls:                      29
% 7.38/1.44  prop_fast_solver_calls:                 1964
% 7.38/1.44  smt_solver_calls:                       0
% 7.38/1.44  smt_fast_solver_calls:                  0
% 7.38/1.44  prop_num_of_clauses:                    4616
% 7.38/1.44  prop_preprocess_simplified:             8702
% 7.38/1.44  prop_fo_subsumed:                       71
% 7.38/1.44  prop_solver_time:                       0.
% 7.38/1.44  smt_solver_time:                        0.
% 7.38/1.44  smt_fast_solver_time:                   0.
% 7.38/1.44  prop_fast_solver_time:                  0.
% 7.38/1.44  prop_unsat_core_time:                   0.
% 7.38/1.44  
% 7.38/1.44  ------ QBF
% 7.38/1.44  
% 7.38/1.44  qbf_q_res:                              0
% 7.38/1.44  qbf_num_tautologies:                    0
% 7.38/1.44  qbf_prep_cycles:                        0
% 7.38/1.44  
% 7.38/1.44  ------ BMC1
% 7.38/1.44  
% 7.38/1.44  bmc1_current_bound:                     -1
% 7.38/1.44  bmc1_last_solved_bound:                 -1
% 7.38/1.44  bmc1_unsat_core_size:                   -1
% 7.38/1.44  bmc1_unsat_core_parents_size:           -1
% 7.38/1.44  bmc1_merge_next_fun:                    0
% 7.38/1.44  bmc1_unsat_core_clauses_time:           0.
% 7.38/1.44  
% 7.38/1.44  ------ Instantiation
% 7.38/1.44  
% 7.38/1.44  inst_num_of_clauses:                    990
% 7.38/1.44  inst_num_in_passive:                    55
% 7.38/1.44  inst_num_in_active:                     568
% 7.38/1.44  inst_num_in_unprocessed:                367
% 7.38/1.44  inst_num_of_loops:                      730
% 7.38/1.44  inst_num_of_learning_restarts:          0
% 7.38/1.44  inst_num_moves_active_passive:          156
% 7.38/1.44  inst_lit_activity:                      0
% 7.38/1.44  inst_lit_activity_moves:                0
% 7.38/1.44  inst_num_tautologies:                   0
% 7.38/1.44  inst_num_prop_implied:                  0
% 7.38/1.44  inst_num_existing_simplified:           0
% 7.38/1.44  inst_num_eq_res_simplified:             0
% 7.38/1.44  inst_num_child_elim:                    0
% 7.38/1.44  inst_num_of_dismatching_blockings:      521
% 7.38/1.44  inst_num_of_non_proper_insts:           1406
% 7.38/1.44  inst_num_of_duplicates:                 0
% 7.38/1.44  inst_inst_num_from_inst_to_res:         0
% 7.38/1.44  inst_dismatching_checking_time:         0.
% 7.38/1.44  
% 7.38/1.44  ------ Resolution
% 7.38/1.44  
% 7.38/1.44  res_num_of_clauses:                     0
% 7.38/1.44  res_num_in_passive:                     0
% 7.38/1.44  res_num_in_active:                      0
% 7.38/1.44  res_num_of_loops:                       126
% 7.38/1.44  res_forward_subset_subsumed:            107
% 7.38/1.44  res_backward_subset_subsumed:           2
% 7.38/1.44  res_forward_subsumed:                   20
% 7.38/1.44  res_backward_subsumed:                  0
% 7.38/1.44  res_forward_subsumption_resolution:     14
% 7.38/1.44  res_backward_subsumption_resolution:    0
% 7.38/1.44  res_clause_to_clause_subsumption:       3622
% 7.38/1.44  res_orphan_elimination:                 0
% 7.38/1.44  res_tautology_del:                      177
% 7.38/1.44  res_num_eq_res_simplified:              0
% 7.38/1.44  res_num_sel_changes:                    0
% 7.38/1.44  res_moves_from_active_to_pass:          0
% 7.38/1.44  
% 7.38/1.44  ------ Superposition
% 7.38/1.44  
% 7.38/1.44  sup_time_total:                         0.
% 7.38/1.44  sup_time_generating:                    0.
% 7.38/1.44  sup_time_sim_full:                      0.
% 7.38/1.44  sup_time_sim_immed:                     0.
% 7.38/1.44  
% 7.38/1.44  sup_num_of_clauses:                     421
% 7.38/1.44  sup_num_in_active:                      139
% 7.38/1.44  sup_num_in_passive:                     282
% 7.38/1.44  sup_num_of_loops:                       144
% 7.38/1.44  sup_fw_superposition:                   361
% 7.38/1.44  sup_bw_superposition:                   252
% 7.38/1.44  sup_immediate_simplified:               110
% 7.38/1.44  sup_given_eliminated:                   0
% 7.38/1.44  comparisons_done:                       0
% 7.38/1.44  comparisons_avoided:                    10
% 7.38/1.44  
% 7.38/1.44  ------ Simplifications
% 7.38/1.44  
% 7.38/1.44  
% 7.38/1.44  sim_fw_subset_subsumed:                 74
% 7.38/1.44  sim_bw_subset_subsumed:                 16
% 7.38/1.44  sim_fw_subsumed:                        23
% 7.38/1.44  sim_bw_subsumed:                        3
% 7.38/1.44  sim_fw_subsumption_res:                 2
% 7.38/1.44  sim_bw_subsumption_res:                 0
% 7.38/1.44  sim_tautology_del:                      8
% 7.38/1.44  sim_eq_tautology_del:                   29
% 7.38/1.44  sim_eq_res_simp:                        0
% 7.38/1.44  sim_fw_demodulated:                     6
% 7.38/1.44  sim_bw_demodulated:                     0
% 7.38/1.44  sim_light_normalised:                   7
% 7.38/1.44  sim_joinable_taut:                      0
% 7.38/1.44  sim_joinable_simp:                      0
% 7.38/1.44  sim_ac_normalised:                      0
% 7.38/1.44  sim_smt_subsumption:                    0
% 7.38/1.44  
%------------------------------------------------------------------------------
