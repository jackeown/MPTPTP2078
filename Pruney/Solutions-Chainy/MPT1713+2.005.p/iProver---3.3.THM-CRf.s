%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:52 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 714 expanded)
%              Number of clauses        :   84 ( 217 expanded)
%              Number of leaves         :   24 ( 189 expanded)
%              Depth                    :   22
%              Number of atoms          :  544 (4304 expanded)
%              Number of equality atoms :  141 ( 235 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( r1_tsep_1(X2,X1)
            | r1_tsep_1(X1,X2) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( r1_tsep_1(sK7,X1)
          | r1_tsep_1(X1,sK7) )
        & m1_pre_topc(X1,sK7)
        & m1_pre_topc(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( r1_tsep_1(X2,sK6)
              | r1_tsep_1(sK6,X2) )
            & m1_pre_topc(sK6,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK5)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( r1_tsep_1(sK7,sK6)
      | r1_tsep_1(sK6,sK7) )
    & m1_pre_topc(sK6,sK7)
    & m1_pre_topc(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f31,f47,f46,f45])).

fof(f83,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( ( r2_hidden(X2,u1_pre_topc(X1))
            <=> ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f33,f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f48])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,u1_pre_topc(X0)) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                  & r2_hidden(X4,u1_pre_topc(X1))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,u1_pre_topc(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ? [X7] :
                      ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
                      & r2_hidden(X7,u1_pre_topc(X1))
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,u1_pre_topc(X0)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                & r2_hidden(X4,u1_pre_topc(X1))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,u1_pre_topc(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1)
              & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f55])).

fof(f85,plain,
    ( r1_tsep_1(sK7,sK6)
    | r1_tsep_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f49,f55,f55])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_631,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_632,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_634,plain,
    ( l1_pre_topc(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_34])).

cnf(c_21,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_10,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_506,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_21,c_10])).

cnf(c_510,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_23])).

cnf(c_511,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_510])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_600,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_511,c_29])).

cnf(c_601,plain,
    ( sP0(sK6,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_641,plain,
    ( sP0(sK6,sK7) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_634,c_601])).

cnf(c_3418,plain,
    ( sP0(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3424,plain,
    ( sP0(X0,X1) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3437,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4656,plain,
    ( k4_xboole_0(k2_struct_0(X0),k4_xboole_0(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0)
    | sP0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3424,c_3437])).

cnf(c_19774,plain,
    ( k4_xboole_0(k2_struct_0(sK6),k4_xboole_0(k2_struct_0(sK6),k2_struct_0(sK7))) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_3418,c_4656])).

cnf(c_28,negated_conjecture,
    ( r1_tsep_1(sK6,sK7)
    | r1_tsep_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3422,plain,
    ( r1_tsep_1(sK6,sK7) = iProver_top
    | r1_tsep_1(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_264,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_26,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_570,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k4_xboole_0(X2,X3) = X2
    | u1_struct_0(X1) != X3
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_264,c_26])).

cnf(c_571,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k4_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_3420,plain,
    ( k4_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0)
    | r1_tsep_1(X0,X1) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_4428,plain,
    ( k4_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(sK6)
    | r1_tsep_1(sK7,sK6) = iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3422,c_3420])).

cnf(c_37,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_43,plain,
    ( r1_tsep_1(sK6,sK7) = iProver_top
    | r1_tsep_1(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_55,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_57,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_struct_0(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_610,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_611,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_612,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_633,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_683,plain,
    ( l1_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_634])).

cnf(c_684,plain,
    ( l1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_685,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_27,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3641,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | r1_tsep_1(sK7,sK6)
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3642,plain,
    ( r1_tsep_1(sK6,sK7) != iProver_top
    | r1_tsep_1(sK7,sK6) = iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3641])).

cnf(c_4676,plain,
    ( r1_tsep_1(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4428,c_37,c_43,c_57,c_612,c_633,c_685,c_3642])).

cnf(c_3423,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5816,plain,
    ( r1_tsep_1(sK6,sK7) = iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4676,c_3423])).

cnf(c_3763,plain,
    ( r1_tsep_1(sK6,sK7)
    | ~ r1_tsep_1(sK7,sK6)
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3764,plain,
    ( r1_tsep_1(sK6,sK7) = iProver_top
    | r1_tsep_1(sK7,sK6) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3763])).

cnf(c_6364,plain,
    ( r1_tsep_1(sK6,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5816,c_37,c_43,c_57,c_612,c_633,c_685,c_3642,c_3764])).

cnf(c_6370,plain,
    ( k4_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(sK6)
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6364,c_3420])).

cnf(c_642,plain,
    ( l1_pre_topc(sK6) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_634,c_611])).

cnf(c_676,plain,
    ( l1_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_642])).

cnf(c_677,plain,
    ( l1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_3415,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3434,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4433,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_3415,c_3434])).

cnf(c_3414,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_4434,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_3414,c_3434])).

cnf(c_6374,plain,
    ( k4_xboole_0(k2_struct_0(sK6),k2_struct_0(sK7)) = k2_struct_0(sK6)
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6370,c_4433,c_4434])).

cnf(c_6380,plain,
    ( k4_xboole_0(k2_struct_0(sK6),k2_struct_0(sK7)) = k2_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6374,c_37,c_57,c_612,c_633,c_685])).

cnf(c_19782,plain,
    ( k4_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) = k2_struct_0(sK6) ),
    inference(light_normalisation,[status(thm)],[c_19774,c_6380])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3868,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3436,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3984,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3868,c_3436])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3435,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4116,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3984,c_3435])).

cnf(c_19783,plain,
    ( k2_struct_0(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19782,c_4116])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_449,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_24])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_477,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_449,c_33])).

cnf(c_478,plain,
    ( ~ l1_struct_0(sK6)
    | u1_struct_0(sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_694,plain,
    ( u1_struct_0(sK6) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_677,c_478])).

cnf(c_5052,plain,
    ( k2_struct_0(sK6) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4433,c_694])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19783,c_5052])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.70/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/0.99  
% 3.70/0.99  ------  iProver source info
% 3.70/0.99  
% 3.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/0.99  git: non_committed_changes: false
% 3.70/0.99  git: last_make_outside_of_git: false
% 3.70/0.99  
% 3.70/0.99  ------ 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options
% 3.70/0.99  
% 3.70/0.99  --out_options                           all
% 3.70/0.99  --tptp_safe_out                         true
% 3.70/0.99  --problem_path                          ""
% 3.70/0.99  --include_path                          ""
% 3.70/0.99  --clausifier                            res/vclausify_rel
% 3.70/0.99  --clausifier_options                    --mode clausify
% 3.70/0.99  --stdin                                 false
% 3.70/0.99  --stats_out                             all
% 3.70/0.99  
% 3.70/0.99  ------ General Options
% 3.70/0.99  
% 3.70/0.99  --fof                                   false
% 3.70/0.99  --time_out_real                         305.
% 3.70/0.99  --time_out_virtual                      -1.
% 3.70/0.99  --symbol_type_check                     false
% 3.70/0.99  --clausify_out                          false
% 3.70/0.99  --sig_cnt_out                           false
% 3.70/0.99  --trig_cnt_out                          false
% 3.70/0.99  --trig_cnt_out_tolerance                1.
% 3.70/0.99  --trig_cnt_out_sk_spl                   false
% 3.70/0.99  --abstr_cl_out                          false
% 3.70/0.99  
% 3.70/0.99  ------ Global Options
% 3.70/0.99  
% 3.70/0.99  --schedule                              default
% 3.70/0.99  --add_important_lit                     false
% 3.70/0.99  --prop_solver_per_cl                    1000
% 3.70/0.99  --min_unsat_core                        false
% 3.70/0.99  --soft_assumptions                      false
% 3.70/0.99  --soft_lemma_size                       3
% 3.70/0.99  --prop_impl_unit_size                   0
% 3.70/0.99  --prop_impl_unit                        []
% 3.70/0.99  --share_sel_clauses                     true
% 3.70/0.99  --reset_solvers                         false
% 3.70/0.99  --bc_imp_inh                            [conj_cone]
% 3.70/0.99  --conj_cone_tolerance                   3.
% 3.70/0.99  --extra_neg_conj                        none
% 3.70/0.99  --large_theory_mode                     true
% 3.70/0.99  --prolific_symb_bound                   200
% 3.70/0.99  --lt_threshold                          2000
% 3.70/0.99  --clause_weak_htbl                      true
% 3.70/0.99  --gc_record_bc_elim                     false
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing Options
% 3.70/0.99  
% 3.70/0.99  --preprocessing_flag                    true
% 3.70/0.99  --time_out_prep_mult                    0.1
% 3.70/0.99  --splitting_mode                        input
% 3.70/0.99  --splitting_grd                         true
% 3.70/0.99  --splitting_cvd                         false
% 3.70/0.99  --splitting_cvd_svl                     false
% 3.70/0.99  --splitting_nvd                         32
% 3.70/0.99  --sub_typing                            true
% 3.70/0.99  --prep_gs_sim                           true
% 3.70/0.99  --prep_unflatten                        true
% 3.70/0.99  --prep_res_sim                          true
% 3.70/0.99  --prep_upred                            true
% 3.70/0.99  --prep_sem_filter                       exhaustive
% 3.70/0.99  --prep_sem_filter_out                   false
% 3.70/0.99  --pred_elim                             true
% 3.70/0.99  --res_sim_input                         true
% 3.70/0.99  --eq_ax_congr_red                       true
% 3.70/0.99  --pure_diseq_elim                       true
% 3.70/0.99  --brand_transform                       false
% 3.70/0.99  --non_eq_to_eq                          false
% 3.70/0.99  --prep_def_merge                        true
% 3.70/0.99  --prep_def_merge_prop_impl              false
% 3.70/0.99  --prep_def_merge_mbd                    true
% 3.70/0.99  --prep_def_merge_tr_red                 false
% 3.70/0.99  --prep_def_merge_tr_cl                  false
% 3.70/0.99  --smt_preprocessing                     true
% 3.70/0.99  --smt_ac_axioms                         fast
% 3.70/0.99  --preprocessed_out                      false
% 3.70/0.99  --preprocessed_stats                    false
% 3.70/0.99  
% 3.70/0.99  ------ Abstraction refinement Options
% 3.70/0.99  
% 3.70/0.99  --abstr_ref                             []
% 3.70/0.99  --abstr_ref_prep                        false
% 3.70/0.99  --abstr_ref_until_sat                   false
% 3.70/0.99  --abstr_ref_sig_restrict                funpre
% 3.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.99  --abstr_ref_under                       []
% 3.70/0.99  
% 3.70/0.99  ------ SAT Options
% 3.70/0.99  
% 3.70/0.99  --sat_mode                              false
% 3.70/0.99  --sat_fm_restart_options                ""
% 3.70/0.99  --sat_gr_def                            false
% 3.70/0.99  --sat_epr_types                         true
% 3.70/0.99  --sat_non_cyclic_types                  false
% 3.70/0.99  --sat_finite_models                     false
% 3.70/0.99  --sat_fm_lemmas                         false
% 3.70/0.99  --sat_fm_prep                           false
% 3.70/0.99  --sat_fm_uc_incr                        true
% 3.70/0.99  --sat_out_model                         small
% 3.70/0.99  --sat_out_clauses                       false
% 3.70/0.99  
% 3.70/0.99  ------ QBF Options
% 3.70/0.99  
% 3.70/0.99  --qbf_mode                              false
% 3.70/0.99  --qbf_elim_univ                         false
% 3.70/0.99  --qbf_dom_inst                          none
% 3.70/0.99  --qbf_dom_pre_inst                      false
% 3.70/0.99  --qbf_sk_in                             false
% 3.70/0.99  --qbf_pred_elim                         true
% 3.70/0.99  --qbf_split                             512
% 3.70/0.99  
% 3.70/0.99  ------ BMC1 Options
% 3.70/0.99  
% 3.70/0.99  --bmc1_incremental                      false
% 3.70/0.99  --bmc1_axioms                           reachable_all
% 3.70/0.99  --bmc1_min_bound                        0
% 3.70/0.99  --bmc1_max_bound                        -1
% 3.70/0.99  --bmc1_max_bound_default                -1
% 3.70/0.99  --bmc1_symbol_reachability              true
% 3.70/0.99  --bmc1_property_lemmas                  false
% 3.70/0.99  --bmc1_k_induction                      false
% 3.70/0.99  --bmc1_non_equiv_states                 false
% 3.70/0.99  --bmc1_deadlock                         false
% 3.70/0.99  --bmc1_ucm                              false
% 3.70/0.99  --bmc1_add_unsat_core                   none
% 3.70/0.99  --bmc1_unsat_core_children              false
% 3.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.99  --bmc1_out_stat                         full
% 3.70/0.99  --bmc1_ground_init                      false
% 3.70/0.99  --bmc1_pre_inst_next_state              false
% 3.70/0.99  --bmc1_pre_inst_state                   false
% 3.70/0.99  --bmc1_pre_inst_reach_state             false
% 3.70/0.99  --bmc1_out_unsat_core                   false
% 3.70/0.99  --bmc1_aig_witness_out                  false
% 3.70/0.99  --bmc1_verbose                          false
% 3.70/0.99  --bmc1_dump_clauses_tptp                false
% 3.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.99  --bmc1_dump_file                        -
% 3.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.99  --bmc1_ucm_extend_mode                  1
% 3.70/0.99  --bmc1_ucm_init_mode                    2
% 3.70/0.99  --bmc1_ucm_cone_mode                    none
% 3.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.99  --bmc1_ucm_relax_model                  4
% 3.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.99  --bmc1_ucm_layered_model                none
% 3.70/0.99  --bmc1_ucm_max_lemma_size               10
% 3.70/0.99  
% 3.70/0.99  ------ AIG Options
% 3.70/0.99  
% 3.70/0.99  --aig_mode                              false
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation Options
% 3.70/0.99  
% 3.70/0.99  --instantiation_flag                    true
% 3.70/0.99  --inst_sos_flag                         false
% 3.70/0.99  --inst_sos_phase                        true
% 3.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel_side                     num_symb
% 3.70/0.99  --inst_solver_per_active                1400
% 3.70/0.99  --inst_solver_calls_frac                1.
% 3.70/0.99  --inst_passive_queue_type               priority_queues
% 3.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.99  --inst_passive_queues_freq              [25;2]
% 3.70/0.99  --inst_dismatching                      true
% 3.70/0.99  --inst_eager_unprocessed_to_passive     true
% 3.70/0.99  --inst_prop_sim_given                   true
% 3.70/0.99  --inst_prop_sim_new                     false
% 3.70/0.99  --inst_subs_new                         false
% 3.70/0.99  --inst_eq_res_simp                      false
% 3.70/0.99  --inst_subs_given                       false
% 3.70/0.99  --inst_orphan_elimination               true
% 3.70/0.99  --inst_learning_loop_flag               true
% 3.70/0.99  --inst_learning_start                   3000
% 3.70/0.99  --inst_learning_factor                  2
% 3.70/0.99  --inst_start_prop_sim_after_learn       3
% 3.70/0.99  --inst_sel_renew                        solver
% 3.70/0.99  --inst_lit_activity_flag                true
% 3.70/0.99  --inst_restr_to_given                   false
% 3.70/0.99  --inst_activity_threshold               500
% 3.70/0.99  --inst_out_proof                        true
% 3.70/0.99  
% 3.70/0.99  ------ Resolution Options
% 3.70/0.99  
% 3.70/0.99  --resolution_flag                       true
% 3.70/0.99  --res_lit_sel                           adaptive
% 3.70/0.99  --res_lit_sel_side                      none
% 3.70/0.99  --res_ordering                          kbo
% 3.70/0.99  --res_to_prop_solver                    active
% 3.70/0.99  --res_prop_simpl_new                    false
% 3.70/0.99  --res_prop_simpl_given                  true
% 3.70/0.99  --res_passive_queue_type                priority_queues
% 3.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.99  --res_passive_queues_freq               [15;5]
% 3.70/0.99  --res_forward_subs                      full
% 3.70/0.99  --res_backward_subs                     full
% 3.70/0.99  --res_forward_subs_resolution           true
% 3.70/0.99  --res_backward_subs_resolution          true
% 3.70/0.99  --res_orphan_elimination                true
% 3.70/0.99  --res_time_limit                        2.
% 3.70/0.99  --res_out_proof                         true
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Options
% 3.70/0.99  
% 3.70/0.99  --superposition_flag                    true
% 3.70/0.99  --sup_passive_queue_type                priority_queues
% 3.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.99  --demod_completeness_check              fast
% 3.70/0.99  --demod_use_ground                      true
% 3.70/0.99  --sup_to_prop_solver                    passive
% 3.70/0.99  --sup_prop_simpl_new                    true
% 3.70/0.99  --sup_prop_simpl_given                  true
% 3.70/0.99  --sup_fun_splitting                     false
% 3.70/0.99  --sup_smt_interval                      50000
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Simplification Setup
% 3.70/0.99  
% 3.70/0.99  --sup_indices_passive                   []
% 3.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_full_bw                           [BwDemod]
% 3.70/0.99  --sup_immed_triv                        [TrivRules]
% 3.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_immed_bw_main                     []
% 3.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  
% 3.70/0.99  ------ Combination Options
% 3.70/0.99  
% 3.70/0.99  --comb_res_mult                         3
% 3.70/0.99  --comb_sup_mult                         2
% 3.70/0.99  --comb_inst_mult                        10
% 3.70/0.99  
% 3.70/0.99  ------ Debug Options
% 3.70/0.99  
% 3.70/0.99  --dbg_backtrace                         false
% 3.70/0.99  --dbg_dump_prop_clauses                 false
% 3.70/0.99  --dbg_dump_prop_clauses_file            -
% 3.70/0.99  --dbg_out_stat                          false
% 3.70/0.99  ------ Parsing...
% 3.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  ------ Proving...
% 3.70/0.99  ------ Problem Properties 
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  clauses                                 29
% 3.70/0.99  conjectures                             1
% 3.70/0.99  EPR                                     9
% 3.70/0.99  Horn                                    24
% 3.70/0.99  unary                                   12
% 3.70/0.99  binary                                  5
% 3.70/0.99  lits                                    72
% 3.70/0.99  lits eq                                 13
% 3.70/0.99  fd_pure                                 0
% 3.70/0.99  fd_pseudo                               0
% 3.70/0.99  fd_cond                                 1
% 3.70/0.99  fd_pseudo_cond                          0
% 3.70/0.99  AC symbols                              0
% 3.70/0.99  
% 3.70/0.99  ------ Schedule dynamic 5 is on 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ 
% 3.70/0.99  Current options:
% 3.70/0.99  ------ 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options
% 3.70/0.99  
% 3.70/0.99  --out_options                           all
% 3.70/0.99  --tptp_safe_out                         true
% 3.70/0.99  --problem_path                          ""
% 3.70/0.99  --include_path                          ""
% 3.70/0.99  --clausifier                            res/vclausify_rel
% 3.70/0.99  --clausifier_options                    --mode clausify
% 3.70/0.99  --stdin                                 false
% 3.70/0.99  --stats_out                             all
% 3.70/0.99  
% 3.70/0.99  ------ General Options
% 3.70/0.99  
% 3.70/0.99  --fof                                   false
% 3.70/0.99  --time_out_real                         305.
% 3.70/0.99  --time_out_virtual                      -1.
% 3.70/0.99  --symbol_type_check                     false
% 3.70/0.99  --clausify_out                          false
% 3.70/0.99  --sig_cnt_out                           false
% 3.70/0.99  --trig_cnt_out                          false
% 3.70/0.99  --trig_cnt_out_tolerance                1.
% 3.70/0.99  --trig_cnt_out_sk_spl                   false
% 3.70/0.99  --abstr_cl_out                          false
% 3.70/0.99  
% 3.70/0.99  ------ Global Options
% 3.70/0.99  
% 3.70/0.99  --schedule                              default
% 3.70/0.99  --add_important_lit                     false
% 3.70/0.99  --prop_solver_per_cl                    1000
% 3.70/0.99  --min_unsat_core                        false
% 3.70/0.99  --soft_assumptions                      false
% 3.70/0.99  --soft_lemma_size                       3
% 3.70/0.99  --prop_impl_unit_size                   0
% 3.70/0.99  --prop_impl_unit                        []
% 3.70/0.99  --share_sel_clauses                     true
% 3.70/0.99  --reset_solvers                         false
% 3.70/0.99  --bc_imp_inh                            [conj_cone]
% 3.70/0.99  --conj_cone_tolerance                   3.
% 3.70/0.99  --extra_neg_conj                        none
% 3.70/0.99  --large_theory_mode                     true
% 3.70/0.99  --prolific_symb_bound                   200
% 3.70/0.99  --lt_threshold                          2000
% 3.70/0.99  --clause_weak_htbl                      true
% 3.70/0.99  --gc_record_bc_elim                     false
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing Options
% 3.70/0.99  
% 3.70/0.99  --preprocessing_flag                    true
% 3.70/0.99  --time_out_prep_mult                    0.1
% 3.70/0.99  --splitting_mode                        input
% 3.70/0.99  --splitting_grd                         true
% 3.70/0.99  --splitting_cvd                         false
% 3.70/0.99  --splitting_cvd_svl                     false
% 3.70/0.99  --splitting_nvd                         32
% 3.70/0.99  --sub_typing                            true
% 3.70/0.99  --prep_gs_sim                           true
% 3.70/0.99  --prep_unflatten                        true
% 3.70/0.99  --prep_res_sim                          true
% 3.70/0.99  --prep_upred                            true
% 3.70/0.99  --prep_sem_filter                       exhaustive
% 3.70/0.99  --prep_sem_filter_out                   false
% 3.70/0.99  --pred_elim                             true
% 3.70/0.99  --res_sim_input                         true
% 3.70/0.99  --eq_ax_congr_red                       true
% 3.70/0.99  --pure_diseq_elim                       true
% 3.70/0.99  --brand_transform                       false
% 3.70/0.99  --non_eq_to_eq                          false
% 3.70/0.99  --prep_def_merge                        true
% 3.70/0.99  --prep_def_merge_prop_impl              false
% 3.70/0.99  --prep_def_merge_mbd                    true
% 3.70/0.99  --prep_def_merge_tr_red                 false
% 3.70/0.99  --prep_def_merge_tr_cl                  false
% 3.70/0.99  --smt_preprocessing                     true
% 3.70/0.99  --smt_ac_axioms                         fast
% 3.70/0.99  --preprocessed_out                      false
% 3.70/0.99  --preprocessed_stats                    false
% 3.70/0.99  
% 3.70/0.99  ------ Abstraction refinement Options
% 3.70/0.99  
% 3.70/0.99  --abstr_ref                             []
% 3.70/0.99  --abstr_ref_prep                        false
% 3.70/0.99  --abstr_ref_until_sat                   false
% 3.70/0.99  --abstr_ref_sig_restrict                funpre
% 3.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.99  --abstr_ref_under                       []
% 3.70/0.99  
% 3.70/0.99  ------ SAT Options
% 3.70/0.99  
% 3.70/0.99  --sat_mode                              false
% 3.70/0.99  --sat_fm_restart_options                ""
% 3.70/0.99  --sat_gr_def                            false
% 3.70/0.99  --sat_epr_types                         true
% 3.70/0.99  --sat_non_cyclic_types                  false
% 3.70/0.99  --sat_finite_models                     false
% 3.70/0.99  --sat_fm_lemmas                         false
% 3.70/0.99  --sat_fm_prep                           false
% 3.70/0.99  --sat_fm_uc_incr                        true
% 3.70/0.99  --sat_out_model                         small
% 3.70/0.99  --sat_out_clauses                       false
% 3.70/0.99  
% 3.70/0.99  ------ QBF Options
% 3.70/0.99  
% 3.70/0.99  --qbf_mode                              false
% 3.70/0.99  --qbf_elim_univ                         false
% 3.70/0.99  --qbf_dom_inst                          none
% 3.70/0.99  --qbf_dom_pre_inst                      false
% 3.70/0.99  --qbf_sk_in                             false
% 3.70/0.99  --qbf_pred_elim                         true
% 3.70/0.99  --qbf_split                             512
% 3.70/0.99  
% 3.70/0.99  ------ BMC1 Options
% 3.70/0.99  
% 3.70/0.99  --bmc1_incremental                      false
% 3.70/0.99  --bmc1_axioms                           reachable_all
% 3.70/0.99  --bmc1_min_bound                        0
% 3.70/0.99  --bmc1_max_bound                        -1
% 3.70/0.99  --bmc1_max_bound_default                -1
% 3.70/0.99  --bmc1_symbol_reachability              true
% 3.70/0.99  --bmc1_property_lemmas                  false
% 3.70/0.99  --bmc1_k_induction                      false
% 3.70/0.99  --bmc1_non_equiv_states                 false
% 3.70/0.99  --bmc1_deadlock                         false
% 3.70/0.99  --bmc1_ucm                              false
% 3.70/0.99  --bmc1_add_unsat_core                   none
% 3.70/0.99  --bmc1_unsat_core_children              false
% 3.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.99  --bmc1_out_stat                         full
% 3.70/0.99  --bmc1_ground_init                      false
% 3.70/0.99  --bmc1_pre_inst_next_state              false
% 3.70/0.99  --bmc1_pre_inst_state                   false
% 3.70/0.99  --bmc1_pre_inst_reach_state             false
% 3.70/0.99  --bmc1_out_unsat_core                   false
% 3.70/0.99  --bmc1_aig_witness_out                  false
% 3.70/0.99  --bmc1_verbose                          false
% 3.70/0.99  --bmc1_dump_clauses_tptp                false
% 3.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.99  --bmc1_dump_file                        -
% 3.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.99  --bmc1_ucm_extend_mode                  1
% 3.70/0.99  --bmc1_ucm_init_mode                    2
% 3.70/0.99  --bmc1_ucm_cone_mode                    none
% 3.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.99  --bmc1_ucm_relax_model                  4
% 3.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.99  --bmc1_ucm_layered_model                none
% 3.70/0.99  --bmc1_ucm_max_lemma_size               10
% 3.70/0.99  
% 3.70/0.99  ------ AIG Options
% 3.70/0.99  
% 3.70/0.99  --aig_mode                              false
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation Options
% 3.70/0.99  
% 3.70/0.99  --instantiation_flag                    true
% 3.70/0.99  --inst_sos_flag                         false
% 3.70/0.99  --inst_sos_phase                        true
% 3.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel_side                     none
% 3.70/0.99  --inst_solver_per_active                1400
% 3.70/0.99  --inst_solver_calls_frac                1.
% 3.70/0.99  --inst_passive_queue_type               priority_queues
% 3.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.99  --inst_passive_queues_freq              [25;2]
% 3.70/0.99  --inst_dismatching                      true
% 3.70/0.99  --inst_eager_unprocessed_to_passive     true
% 3.70/0.99  --inst_prop_sim_given                   true
% 3.70/0.99  --inst_prop_sim_new                     false
% 3.70/0.99  --inst_subs_new                         false
% 3.70/0.99  --inst_eq_res_simp                      false
% 3.70/0.99  --inst_subs_given                       false
% 3.70/0.99  --inst_orphan_elimination               true
% 3.70/0.99  --inst_learning_loop_flag               true
% 3.70/0.99  --inst_learning_start                   3000
% 3.70/0.99  --inst_learning_factor                  2
% 3.70/0.99  --inst_start_prop_sim_after_learn       3
% 3.70/0.99  --inst_sel_renew                        solver
% 3.70/0.99  --inst_lit_activity_flag                true
% 3.70/0.99  --inst_restr_to_given                   false
% 3.70/0.99  --inst_activity_threshold               500
% 3.70/0.99  --inst_out_proof                        true
% 3.70/0.99  
% 3.70/0.99  ------ Resolution Options
% 3.70/0.99  
% 3.70/0.99  --resolution_flag                       false
% 3.70/0.99  --res_lit_sel                           adaptive
% 3.70/0.99  --res_lit_sel_side                      none
% 3.70/0.99  --res_ordering                          kbo
% 3.70/0.99  --res_to_prop_solver                    active
% 3.70/0.99  --res_prop_simpl_new                    false
% 3.70/0.99  --res_prop_simpl_given                  true
% 3.70/0.99  --res_passive_queue_type                priority_queues
% 3.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.99  --res_passive_queues_freq               [15;5]
% 3.70/0.99  --res_forward_subs                      full
% 3.70/0.99  --res_backward_subs                     full
% 3.70/0.99  --res_forward_subs_resolution           true
% 3.70/0.99  --res_backward_subs_resolution          true
% 3.70/0.99  --res_orphan_elimination                true
% 3.70/0.99  --res_time_limit                        2.
% 3.70/0.99  --res_out_proof                         true
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Options
% 3.70/0.99  
% 3.70/0.99  --superposition_flag                    true
% 3.70/0.99  --sup_passive_queue_type                priority_queues
% 3.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.99  --demod_completeness_check              fast
% 3.70/0.99  --demod_use_ground                      true
% 3.70/0.99  --sup_to_prop_solver                    passive
% 3.70/0.99  --sup_prop_simpl_new                    true
% 3.70/0.99  --sup_prop_simpl_given                  true
% 3.70/0.99  --sup_fun_splitting                     false
% 3.70/0.99  --sup_smt_interval                      50000
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Simplification Setup
% 3.70/0.99  
% 3.70/0.99  --sup_indices_passive                   []
% 3.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_full_bw                           [BwDemod]
% 3.70/0.99  --sup_immed_triv                        [TrivRules]
% 3.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_immed_bw_main                     []
% 3.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  
% 3.70/0.99  ------ Combination Options
% 3.70/0.99  
% 3.70/0.99  --comb_res_mult                         3
% 3.70/0.99  --comb_sup_mult                         2
% 3.70/0.99  --comb_inst_mult                        10
% 3.70/0.99  
% 3.70/0.99  ------ Debug Options
% 3.70/0.99  
% 3.70/0.99  --dbg_backtrace                         false
% 3.70/0.99  --dbg_dump_prop_clauses                 false
% 3.70/0.99  --dbg_dump_prop_clauses_file            -
% 3.70/0.99  --dbg_out_stat                          false
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS status Theorem for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  fof(f12,axiom,(
% 3.70/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f24,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f12])).
% 3.70/0.99  
% 3.70/0.99  fof(f73,plain,(
% 3.70/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f24])).
% 3.70/0.99  
% 3.70/0.99  fof(f16,conjecture,(
% 3.70/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f17,negated_conjecture,(
% 3.70/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 3.70/0.99    inference(negated_conjecture,[],[f16])).
% 3.70/0.99  
% 3.70/0.99  fof(f18,plain,(
% 3.70/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 3.70/0.99    inference(pure_predicate_removal,[],[f17])).
% 3.70/0.99  
% 3.70/0.99  fof(f30,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f18])).
% 3.70/0.99  
% 3.70/0.99  fof(f31,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.70/0.99    inference(flattening,[],[f30])).
% 3.70/0.99  
% 3.70/0.99  fof(f47,plain,(
% 3.70/0.99    ( ! [X0,X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((r1_tsep_1(sK7,X1) | r1_tsep_1(X1,sK7)) & m1_pre_topc(X1,sK7) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f46,plain,(
% 3.70/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((r1_tsep_1(X2,sK6) | r1_tsep_1(sK6,X2)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f45,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f48,plain,(
% 3.70/0.99    (((r1_tsep_1(sK7,sK6) | r1_tsep_1(sK6,sK7)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f31,f47,f46,f45])).
% 3.70/0.99  
% 3.70/0.99  fof(f83,plain,(
% 3.70/0.99    m1_pre_topc(sK7,sK5)),
% 3.70/0.99    inference(cnf_transformation,[],[f48])).
% 3.70/0.99  
% 3.70/0.99  fof(f79,plain,(
% 3.70/0.99    l1_pre_topc(sK5)),
% 3.70/0.99    inference(cnf_transformation,[],[f48])).
% 3.70/0.99  
% 3.70/0.99  fof(f10,axiom,(
% 3.70/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f22,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f10])).
% 3.70/0.99  
% 3.70/0.99  fof(f33,plain,(
% 3.70/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 3.70/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.70/0.99  
% 3.70/0.99  fof(f32,plain,(
% 3.70/0.99    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 3.70/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.70/0.99  
% 3.70/0.99  fof(f34,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(definition_folding,[],[f22,f33,f32])).
% 3.70/0.99  
% 3.70/0.99  fof(f71,plain,(
% 3.70/0.99    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f34])).
% 3.70/0.99  
% 3.70/0.99  fof(f36,plain,(
% 3.70/0.99    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 3.70/0.99    inference(nnf_transformation,[],[f33])).
% 3.70/0.99  
% 3.70/0.99  fof(f59,plain,(
% 3.70/0.99    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f36])).
% 3.70/0.99  
% 3.70/0.99  fof(f84,plain,(
% 3.70/0.99    m1_pre_topc(sK6,sK7)),
% 3.70/0.99    inference(cnf_transformation,[],[f48])).
% 3.70/0.99  
% 3.70/0.99  fof(f37,plain,(
% 3.70/0.99    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.70/0.99    inference(nnf_transformation,[],[f32])).
% 3.70/0.99  
% 3.70/0.99  fof(f38,plain,(
% 3.70/0.99    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.70/0.99    inference(flattening,[],[f37])).
% 3.70/0.99  
% 3.70/0.99  fof(f39,plain,(
% 3.70/0.99    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.70/0.99    inference(rectify,[],[f38])).
% 3.70/0.99  
% 3.70/0.99  fof(f42,plain,(
% 3.70/0.99    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f41,plain,(
% 3.70/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f40,plain,(
% 3.70/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f43,plain,(
% 3.70/0.99    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).
% 3.70/0.99  
% 3.70/0.99  fof(f61,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f43])).
% 3.70/0.99  
% 3.70/0.99  fof(f3,axiom,(
% 3.70/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f19,plain,(
% 3.70/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.70/0.99    inference(ennf_transformation,[],[f3])).
% 3.70/0.99  
% 3.70/0.99  fof(f51,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f19])).
% 3.70/0.99  
% 3.70/0.99  fof(f7,axiom,(
% 3.70/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f55,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f7])).
% 3.70/0.99  
% 3.70/0.99  fof(f87,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.70/0.99    inference(definition_unfolding,[],[f51,f55])).
% 3.70/0.99  
% 3.70/0.99  fof(f85,plain,(
% 3.70/0.99    r1_tsep_1(sK7,sK6) | r1_tsep_1(sK6,sK7)),
% 3.70/0.99    inference(cnf_transformation,[],[f48])).
% 3.70/0.99  
% 3.70/0.99  fof(f8,axiom,(
% 3.70/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f35,plain,(
% 3.70/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.70/0.99    inference(nnf_transformation,[],[f8])).
% 3.70/0.99  
% 3.70/0.99  fof(f56,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f35])).
% 3.70/0.99  
% 3.70/0.99  fof(f14,axiom,(
% 3.70/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f27,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f14])).
% 3.70/0.99  
% 3.70/0.99  fof(f44,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f27])).
% 3.70/0.99  
% 3.70/0.99  fof(f75,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f11,axiom,(
% 3.70/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f23,plain,(
% 3.70/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f11])).
% 3.70/0.99  
% 3.70/0.99  fof(f72,plain,(
% 3.70/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f23])).
% 3.70/0.99  
% 3.70/0.99  fof(f15,axiom,(
% 3.70/0.99    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f28,plain,(
% 3.70/0.99    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f15])).
% 3.70/0.99  
% 3.70/0.99  fof(f29,plain,(
% 3.70/0.99    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.70/0.99    inference(flattening,[],[f28])).
% 3.70/0.99  
% 3.70/0.99  fof(f77,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f29])).
% 3.70/0.99  
% 3.70/0.99  fof(f9,axiom,(
% 3.70/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f21,plain,(
% 3.70/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f9])).
% 3.70/0.99  
% 3.70/0.99  fof(f58,plain,(
% 3.70/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f21])).
% 3.70/0.99  
% 3.70/0.99  fof(f5,axiom,(
% 3.70/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f53,plain,(
% 3.70/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.70/0.99    inference(cnf_transformation,[],[f5])).
% 3.70/0.99  
% 3.70/0.99  fof(f1,axiom,(
% 3.70/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f49,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f1])).
% 3.70/0.99  
% 3.70/0.99  fof(f86,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.70/0.99    inference(definition_unfolding,[],[f49,f55,f55])).
% 3.70/0.99  
% 3.70/0.99  fof(f4,axiom,(
% 3.70/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f52,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f4])).
% 3.70/0.99  
% 3.70/0.99  fof(f6,axiom,(
% 3.70/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f20,plain,(
% 3.70/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.70/0.99    inference(ennf_transformation,[],[f6])).
% 3.70/0.99  
% 3.70/0.99  fof(f54,plain,(
% 3.70/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f20])).
% 3.70/0.99  
% 3.70/0.99  fof(f2,axiom,(
% 3.70/0.99    v1_xboole_0(k1_xboole_0)),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f50,plain,(
% 3.70/0.99    v1_xboole_0(k1_xboole_0)),
% 3.70/0.99    inference(cnf_transformation,[],[f2])).
% 3.70/0.99  
% 3.70/0.99  fof(f13,axiom,(
% 3.70/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f25,plain,(
% 3.70/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f13])).
% 3.70/0.99  
% 3.70/0.99  fof(f26,plain,(
% 3.70/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.70/0.99    inference(flattening,[],[f25])).
% 3.70/0.99  
% 3.70/0.99  fof(f74,plain,(
% 3.70/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f26])).
% 3.70/0.99  
% 3.70/0.99  fof(f80,plain,(
% 3.70/0.99    ~v2_struct_0(sK6)),
% 3.70/0.99    inference(cnf_transformation,[],[f48])).
% 3.70/0.99  
% 3.70/0.99  cnf(c_23,plain,
% 3.70/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_30,negated_conjecture,
% 3.70/0.99      ( m1_pre_topc(sK7,sK5) ),
% 3.70/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_631,plain,
% 3.70/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK5 != X0 | sK7 != X1 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_632,plain,
% 3.70/0.99      ( ~ l1_pre_topc(sK5) | l1_pre_topc(sK7) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_631]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_34,negated_conjecture,
% 3.70/0.99      ( l1_pre_topc(sK5) ),
% 3.70/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_634,plain,
% 3.70/0.99      ( l1_pre_topc(sK7) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_632,c_34]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_21,plain,
% 3.70/0.99      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_10,plain,
% 3.70/0.99      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_506,plain,
% 3.70/0.99      ( sP0(X0,X1)
% 3.70/0.99      | ~ m1_pre_topc(X0,X1)
% 3.70/0.99      | ~ l1_pre_topc(X1)
% 3.70/0.99      | ~ l1_pre_topc(X0) ),
% 3.70/0.99      inference(resolution,[status(thm)],[c_21,c_10]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_510,plain,
% 3.70/0.99      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_506,c_23]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_511,plain,
% 3.70/0.99      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_510]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_29,negated_conjecture,
% 3.70/0.99      ( m1_pre_topc(sK6,sK7) ),
% 3.70/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_600,plain,
% 3.70/0.99      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK6 != X0 | sK7 != X1 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_511,c_29]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_601,plain,
% 3.70/0.99      ( sP0(sK6,sK7) | ~ l1_pre_topc(sK7) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_600]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_641,plain,
% 3.70/0.99      ( sP0(sK6,sK7) ),
% 3.70/0.99      inference(backward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_634,c_601]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3418,plain,
% 3.70/0.99      ( sP0(sK6,sK7) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_20,plain,
% 3.70/0.99      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3424,plain,
% 3.70/0.99      ( sP0(X0,X1) != iProver_top
% 3.70/0.99      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2,plain,
% 3.70/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3437,plain,
% 3.70/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.70/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4656,plain,
% 3.70/0.99      ( k4_xboole_0(k2_struct_0(X0),k4_xboole_0(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0)
% 3.70/0.99      | sP0(X0,X1) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_3424,c_3437]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_19774,plain,
% 3.70/0.99      ( k4_xboole_0(k2_struct_0(sK6),k4_xboole_0(k2_struct_0(sK6),k2_struct_0(sK7))) = k2_struct_0(sK6) ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_3418,c_4656]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_28,negated_conjecture,
% 3.70/0.99      ( r1_tsep_1(sK6,sK7) | r1_tsep_1(sK7,sK6) ),
% 3.70/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3422,plain,
% 3.70/0.99      ( r1_tsep_1(sK6,sK7) = iProver_top
% 3.70/0.99      | r1_tsep_1(sK7,sK6) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_7,plain,
% 3.70/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_264,plain,
% 3.70/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.70/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_26,plain,
% 3.70/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.70/0.99      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.70/0.99      | ~ l1_struct_0(X0)
% 3.70/0.99      | ~ l1_struct_0(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_570,plain,
% 3.70/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.70/0.99      | ~ l1_struct_0(X0)
% 3.70/0.99      | ~ l1_struct_0(X1)
% 3.70/0.99      | k4_xboole_0(X2,X3) = X2
% 3.70/0.99      | u1_struct_0(X1) != X3
% 3.70/0.99      | u1_struct_0(X0) != X2 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_264,c_26]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_571,plain,
% 3.70/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.70/0.99      | ~ l1_struct_0(X0)
% 3.70/0.99      | ~ l1_struct_0(X1)
% 3.70/0.99      | k4_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_570]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3420,plain,
% 3.70/0.99      ( k4_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0)
% 3.70/0.99      | r1_tsep_1(X0,X1) != iProver_top
% 3.70/0.99      | l1_struct_0(X0) != iProver_top
% 3.70/0.99      | l1_struct_0(X1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4428,plain,
% 3.70/0.99      ( k4_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(sK6)
% 3.70/0.99      | r1_tsep_1(sK7,sK6) = iProver_top
% 3.70/0.99      | l1_struct_0(sK6) != iProver_top
% 3.70/0.99      | l1_struct_0(sK7) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_3422,c_3420]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_37,plain,
% 3.70/0.99      ( l1_pre_topc(sK5) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_43,plain,
% 3.70/0.99      ( r1_tsep_1(sK6,sK7) = iProver_top
% 3.70/0.99      | r1_tsep_1(sK7,sK6) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_22,plain,
% 3.70/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_55,plain,
% 3.70/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_57,plain,
% 3.70/0.99      ( l1_pre_topc(sK6) != iProver_top
% 3.70/0.99      | l1_struct_0(sK6) = iProver_top ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_55]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_610,plain,
% 3.70/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X1 | sK7 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_611,plain,
% 3.70/0.99      ( l1_pre_topc(sK6) | ~ l1_pre_topc(sK7) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_610]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_612,plain,
% 3.70/0.99      ( l1_pre_topc(sK6) = iProver_top
% 3.70/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_633,plain,
% 3.70/0.99      ( l1_pre_topc(sK5) != iProver_top
% 3.70/0.99      | l1_pre_topc(sK7) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_683,plain,
% 3.70/0.99      ( l1_struct_0(X0) | sK7 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_634]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_684,plain,
% 3.70/0.99      ( l1_struct_0(sK7) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_683]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_685,plain,
% 3.70/0.99      ( l1_struct_0(sK7) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_684]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_27,plain,
% 3.70/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.70/0.99      | r1_tsep_1(X1,X0)
% 3.70/0.99      | ~ l1_struct_0(X0)
% 3.70/0.99      | ~ l1_struct_0(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3641,plain,
% 3.70/0.99      ( ~ r1_tsep_1(sK6,sK7)
% 3.70/0.99      | r1_tsep_1(sK7,sK6)
% 3.70/0.99      | ~ l1_struct_0(sK6)
% 3.70/0.99      | ~ l1_struct_0(sK7) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3642,plain,
% 3.70/0.99      ( r1_tsep_1(sK6,sK7) != iProver_top
% 3.70/0.99      | r1_tsep_1(sK7,sK6) = iProver_top
% 3.70/0.99      | l1_struct_0(sK6) != iProver_top
% 3.70/0.99      | l1_struct_0(sK7) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_3641]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4676,plain,
% 3.70/0.99      ( r1_tsep_1(sK7,sK6) = iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_4428,c_37,c_43,c_57,c_612,c_633,c_685,c_3642]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3423,plain,
% 3.70/0.99      ( r1_tsep_1(X0,X1) != iProver_top
% 3.70/0.99      | r1_tsep_1(X1,X0) = iProver_top
% 3.70/0.99      | l1_struct_0(X0) != iProver_top
% 3.70/0.99      | l1_struct_0(X1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5816,plain,
% 3.70/0.99      ( r1_tsep_1(sK6,sK7) = iProver_top
% 3.70/0.99      | l1_struct_0(sK6) != iProver_top
% 3.70/0.99      | l1_struct_0(sK7) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4676,c_3423]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3763,plain,
% 3.70/0.99      ( r1_tsep_1(sK6,sK7)
% 3.70/0.99      | ~ r1_tsep_1(sK7,sK6)
% 3.70/0.99      | ~ l1_struct_0(sK6)
% 3.70/0.99      | ~ l1_struct_0(sK7) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3764,plain,
% 3.70/0.99      ( r1_tsep_1(sK6,sK7) = iProver_top
% 3.70/0.99      | r1_tsep_1(sK7,sK6) != iProver_top
% 3.70/0.99      | l1_struct_0(sK6) != iProver_top
% 3.70/0.99      | l1_struct_0(sK7) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_3763]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6364,plain,
% 3.70/0.99      ( r1_tsep_1(sK6,sK7) = iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_5816,c_37,c_43,c_57,c_612,c_633,c_685,c_3642,c_3764]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6370,plain,
% 3.70/0.99      ( k4_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(sK6)
% 3.70/0.99      | l1_struct_0(sK6) != iProver_top
% 3.70/0.99      | l1_struct_0(sK7) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_6364,c_3420]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_642,plain,
% 3.70/0.99      ( l1_pre_topc(sK6) ),
% 3.70/0.99      inference(backward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_634,c_611]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_676,plain,
% 3.70/0.99      ( l1_struct_0(X0) | sK6 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_642]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_677,plain,
% 3.70/0.99      ( l1_struct_0(sK6) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_676]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3415,plain,
% 3.70/0.99      ( l1_struct_0(sK6) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8,plain,
% 3.70/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3434,plain,
% 3.70/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.70/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4433,plain,
% 3.70/0.99      ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_3415,c_3434]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3414,plain,
% 3.70/0.99      ( l1_struct_0(sK7) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_684]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4434,plain,
% 3.70/0.99      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_3414,c_3434]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6374,plain,
% 3.70/0.99      ( k4_xboole_0(k2_struct_0(sK6),k2_struct_0(sK7)) = k2_struct_0(sK6)
% 3.70/0.99      | l1_struct_0(sK6) != iProver_top
% 3.70/0.99      | l1_struct_0(sK7) != iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_6370,c_4433,c_4434]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6380,plain,
% 3.70/0.99      ( k4_xboole_0(k2_struct_0(sK6),k2_struct_0(sK7)) = k2_struct_0(sK6) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_6374,c_37,c_57,c_612,c_633,c_685]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_19782,plain,
% 3.70/0.99      ( k4_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) = k2_struct_0(sK6) ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_19774,c_6380]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4,plain,
% 3.70/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_0,plain,
% 3.70/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3868,plain,
% 3.70/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3,plain,
% 3.70/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3436,plain,
% 3.70/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3984,plain,
% 3.70/0.99      ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_3868,c_3436]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5,plain,
% 3.70/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3435,plain,
% 3.70/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4116,plain,
% 3.70/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_3984,c_3435]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_19783,plain,
% 3.70/0.99      ( k2_struct_0(sK6) = k1_xboole_0 ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_19782,c_4116]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1,plain,
% 3.70/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_24,plain,
% 3.70/0.99      ( v2_struct_0(X0)
% 3.70/0.99      | ~ l1_struct_0(X0)
% 3.70/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_449,plain,
% 3.70/0.99      ( v2_struct_0(X0)
% 3.70/0.99      | ~ l1_struct_0(X0)
% 3.70/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_24]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_33,negated_conjecture,
% 3.70/0.99      ( ~ v2_struct_0(sK6) ),
% 3.70/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_477,plain,
% 3.70/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK6 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_449,c_33]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_478,plain,
% 3.70/0.99      ( ~ l1_struct_0(sK6) | u1_struct_0(sK6) != k1_xboole_0 ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_477]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_694,plain,
% 3.70/0.99      ( u1_struct_0(sK6) != k1_xboole_0 ),
% 3.70/0.99      inference(backward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_677,c_478]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5052,plain,
% 3.70/0.99      ( k2_struct_0(sK6) != k1_xboole_0 ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_4433,c_694]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(contradiction,plain,
% 3.70/0.99      ( $false ),
% 3.70/0.99      inference(minisat,[status(thm)],[c_19783,c_5052]) ).
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  ------                               Statistics
% 3.70/0.99  
% 3.70/0.99  ------ General
% 3.70/0.99  
% 3.70/0.99  abstr_ref_over_cycles:                  0
% 3.70/0.99  abstr_ref_under_cycles:                 0
% 3.70/0.99  gc_basic_clause_elim:                   0
% 3.70/0.99  forced_gc_time:                         0
% 3.70/0.99  parsing_time:                           0.009
% 3.70/0.99  unif_index_cands_time:                  0.
% 3.70/0.99  unif_index_add_time:                    0.
% 3.70/0.99  orderings_time:                         0.
% 3.70/0.99  out_proof_time:                         0.011
% 3.70/0.99  total_time:                             0.481
% 3.70/0.99  num_of_symbols:                         56
% 3.70/0.99  num_of_terms:                           15854
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing
% 3.70/0.99  
% 3.70/0.99  num_of_splits:                          0
% 3.70/0.99  num_of_split_atoms:                     0
% 3.70/0.99  num_of_reused_defs:                     0
% 3.70/0.99  num_eq_ax_congr_red:                    34
% 3.70/0.99  num_of_sem_filtered_clauses:            1
% 3.70/0.99  num_of_subtypes:                        0
% 3.70/0.99  monotx_restored_types:                  0
% 3.70/0.99  sat_num_of_epr_types:                   0
% 3.70/0.99  sat_num_of_non_cyclic_types:            0
% 3.70/0.99  sat_guarded_non_collapsed_types:        0
% 3.70/0.99  num_pure_diseq_elim:                    0
% 3.70/0.99  simp_replaced_by:                       0
% 3.70/0.99  res_preprocessed:                       148
% 3.70/0.99  prep_upred:                             0
% 3.70/0.99  prep_unflattend:                        186
% 3.70/0.99  smt_new_axioms:                         0
% 3.70/0.99  pred_elim_cands:                        6
% 3.70/0.99  pred_elim:                              6
% 3.70/0.99  pred_elim_cl:                           7
% 3.70/0.99  pred_elim_cycles:                       10
% 3.70/0.99  merged_defs:                            2
% 3.70/0.99  merged_defs_ncl:                        0
% 3.70/0.99  bin_hyper_res:                          2
% 3.70/0.99  prep_cycles:                            4
% 3.70/0.99  pred_elim_time:                         0.03
% 3.70/0.99  splitting_time:                         0.
% 3.70/0.99  sem_filter_time:                        0.
% 3.70/0.99  monotx_time:                            0.
% 3.70/0.99  subtype_inf_time:                       0.
% 3.70/0.99  
% 3.70/0.99  ------ Problem properties
% 3.70/0.99  
% 3.70/0.99  clauses:                                29
% 3.70/0.99  conjectures:                            1
% 3.70/0.99  epr:                                    9
% 3.70/0.99  horn:                                   24
% 3.70/0.99  ground:                                 10
% 3.70/0.99  unary:                                  12
% 3.70/0.99  binary:                                 5
% 3.70/0.99  lits:                                   72
% 3.70/0.99  lits_eq:                                13
% 3.70/0.99  fd_pure:                                0
% 3.70/0.99  fd_pseudo:                              0
% 3.70/0.99  fd_cond:                                1
% 3.70/0.99  fd_pseudo_cond:                         0
% 3.70/0.99  ac_symbols:                             0
% 3.70/0.99  
% 3.70/0.99  ------ Propositional Solver
% 3.70/0.99  
% 3.70/0.99  prop_solver_calls:                      30
% 3.70/0.99  prop_fast_solver_calls:                 2044
% 3.70/0.99  smt_solver_calls:                       0
% 3.70/0.99  smt_fast_solver_calls:                  0
% 3.70/0.99  prop_num_of_clauses:                    5610
% 3.70/0.99  prop_preprocess_simplified:             12273
% 3.70/0.99  prop_fo_subsumed:                       37
% 3.70/0.99  prop_solver_time:                       0.
% 3.70/0.99  smt_solver_time:                        0.
% 3.70/0.99  smt_fast_solver_time:                   0.
% 3.70/0.99  prop_fast_solver_time:                  0.
% 3.70/0.99  prop_unsat_core_time:                   0.
% 3.70/0.99  
% 3.70/0.99  ------ QBF
% 3.70/0.99  
% 3.70/0.99  qbf_q_res:                              0
% 3.70/0.99  qbf_num_tautologies:                    0
% 3.70/0.99  qbf_prep_cycles:                        0
% 3.70/0.99  
% 3.70/0.99  ------ BMC1
% 3.70/0.99  
% 3.70/0.99  bmc1_current_bound:                     -1
% 3.70/0.99  bmc1_last_solved_bound:                 -1
% 3.70/0.99  bmc1_unsat_core_size:                   -1
% 3.70/0.99  bmc1_unsat_core_parents_size:           -1
% 3.70/0.99  bmc1_merge_next_fun:                    0
% 3.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation
% 3.70/0.99  
% 3.70/0.99  inst_num_of_clauses:                    1725
% 3.70/0.99  inst_num_in_passive:                    692
% 3.70/0.99  inst_num_in_active:                     765
% 3.70/0.99  inst_num_in_unprocessed:                270
% 3.70/0.99  inst_num_of_loops:                      780
% 3.70/0.99  inst_num_of_learning_restarts:          0
% 3.70/0.99  inst_num_moves_active_passive:          10
% 3.70/0.99  inst_lit_activity:                      0
% 3.70/0.99  inst_lit_activity_moves:                0
% 3.70/0.99  inst_num_tautologies:                   0
% 3.70/0.99  inst_num_prop_implied:                  0
% 3.70/0.99  inst_num_existing_simplified:           0
% 3.70/0.99  inst_num_eq_res_simplified:             0
% 3.70/0.99  inst_num_child_elim:                    0
% 3.70/0.99  inst_num_of_dismatching_blockings:      1205
% 3.70/0.99  inst_num_of_non_proper_insts:           1951
% 3.70/0.99  inst_num_of_duplicates:                 0
% 3.70/0.99  inst_inst_num_from_inst_to_res:         0
% 3.70/0.99  inst_dismatching_checking_time:         0.
% 3.70/0.99  
% 3.70/0.99  ------ Resolution
% 3.70/0.99  
% 3.70/0.99  res_num_of_clauses:                     0
% 3.70/0.99  res_num_in_passive:                     0
% 3.70/0.99  res_num_in_active:                      0
% 3.70/0.99  res_num_of_loops:                       152
% 3.70/0.99  res_forward_subset_subsumed:            180
% 3.70/0.99  res_backward_subset_subsumed:           10
% 3.70/0.99  res_forward_subsumed:                   0
% 3.70/0.99  res_backward_subsumed:                  0
% 3.70/0.99  res_forward_subsumption_resolution:     0
% 3.70/0.99  res_backward_subsumption_resolution:    5
% 3.70/0.99  res_clause_to_clause_subsumption:       2001
% 3.70/0.99  res_orphan_elimination:                 0
% 3.70/0.99  res_tautology_del:                      178
% 3.70/0.99  res_num_eq_res_simplified:              0
% 3.70/0.99  res_num_sel_changes:                    0
% 3.70/0.99  res_moves_from_active_to_pass:          0
% 3.70/0.99  
% 3.70/0.99  ------ Superposition
% 3.70/0.99  
% 3.70/0.99  sup_time_total:                         0.
% 3.70/0.99  sup_time_generating:                    0.
% 3.70/0.99  sup_time_sim_full:                      0.
% 3.70/0.99  sup_time_sim_immed:                     0.
% 3.70/0.99  
% 3.70/0.99  sup_num_of_clauses:                     348
% 3.70/0.99  sup_num_in_active:                      131
% 3.70/0.99  sup_num_in_passive:                     217
% 3.70/0.99  sup_num_of_loops:                       154
% 3.70/0.99  sup_fw_superposition:                   808
% 3.70/0.99  sup_bw_superposition:                   269
% 3.70/0.99  sup_immediate_simplified:               455
% 3.70/0.99  sup_given_eliminated:                   1
% 3.70/0.99  comparisons_done:                       0
% 3.70/0.99  comparisons_avoided:                    0
% 3.70/0.99  
% 3.70/0.99  ------ Simplifications
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  sim_fw_subset_subsumed:                 11
% 3.70/0.99  sim_bw_subset_subsumed:                 1
% 3.70/0.99  sim_fw_subsumed:                        62
% 3.70/0.99  sim_bw_subsumed:                        1
% 3.70/0.99  sim_fw_subsumption_res:                 18
% 3.70/0.99  sim_bw_subsumption_res:                 0
% 3.70/0.99  sim_tautology_del:                      2
% 3.70/0.99  sim_eq_tautology_del:                   105
% 3.70/0.99  sim_eq_res_simp:                        0
% 3.70/0.99  sim_fw_demodulated:                     344
% 3.70/0.99  sim_bw_demodulated:                     26
% 3.70/0.99  sim_light_normalised:                   317
% 3.70/0.99  sim_joinable_taut:                      0
% 3.70/0.99  sim_joinable_simp:                      0
% 3.70/0.99  sim_ac_normalised:                      0
% 3.70/0.99  sim_smt_subsumption:                    0
% 3.70/0.99  
%------------------------------------------------------------------------------
