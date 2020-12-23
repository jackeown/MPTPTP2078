%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:26 EST 2020

% Result     : CounterSatisfiable 2.32s
% Output     : Saturation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 814 expanded)
%              Number of clauses        :   79 ( 214 expanded)
%              Number of leaves         :   18 ( 286 expanded)
%              Depth                    :   13
%              Number of atoms          :  495 (5545 expanded)
%              Number of equality atoms :  174 (1703 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,plain,(
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

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).

fof(f34,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f8,f14,f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( l1_pre_topc(X2)
               => ! [X3] :
                    ( l1_pre_topc(X3)
                   => ( ( m1_pre_topc(X2,X0)
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(X3,X1)
                  & m1_pre_topc(X2,X0)
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & l1_pre_topc(X3) )
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(X3,X1)
                  & m1_pre_topc(X2,X0)
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & l1_pre_topc(X3) )
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_pre_topc(X3,X1)
          & m1_pre_topc(X2,X0)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X3) )
     => ( ~ m1_pre_topc(sK8,X1)
        & m1_pre_topc(X2,X0)
        & g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & l1_pre_topc(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(X3,X1)
              & m1_pre_topc(X2,X0)
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
              & l1_pre_topc(X3) )
          & l1_pre_topc(X2) )
     => ( ? [X3] :
            ( ~ m1_pre_topc(X3,X1)
            & m1_pre_topc(sK7,X0)
            & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X3) )
        & l1_pre_topc(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(X3,X1)
                  & m1_pre_topc(X2,X0)
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & l1_pre_topc(X3) )
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(X3,sK6)
                & m1_pre_topc(X2,X0)
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
                & l1_pre_topc(X3) )
            & l1_pre_topc(X2) )
        & l1_pre_topc(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(X3,X1)
                    & m1_pre_topc(X2,X0)
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & l1_pre_topc(X3) )
                & l1_pre_topc(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(X3,X1)
                  & m1_pre_topc(X2,sK5)
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & l1_pre_topc(X3) )
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    & m1_pre_topc(sK7,sK5)
    & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
    & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    & l1_pre_topc(sK8)
    & l1_pre_topc(sK7)
    & l1_pre_topc(sK6)
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f12,f27,f26,f25,f24])).

fof(f51,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f28])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f49,plain,(
    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ~ m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2)
    | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_256,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | sK5 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_257,plain,
    ( ~ sP1(sK5,sK7)
    | sP0(sK7,sK5) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_292,plain,
    ( sP0(sK7,sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK5 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_257])).

cnf(c_293,plain,
    ( sP0(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_295,plain,
    ( sP0(sK7,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_293,c_23,c_21])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0
    | sK5 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_295])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X0,u1_pre_topc(sK7))
    | k9_subset_1(u1_struct_0(sK7),sK4(sK7,sK5,X0),k2_struct_0(sK7)) = X0 ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(sK4(X1,X2,X0),u1_pre_topc(X2))
    | ~ sP0(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(sK4(X1,X2,X0),u1_pre_topc(X2))
    | sK5 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_295])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X0,u1_pre_topc(sK7))
    | r2_hidden(sK4(sK7,sK5,X0),u1_pre_topc(sK5)) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | sK5 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_295])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK4(sK7,sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,u1_pre_topc(sK7)) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),u1_pre_topc(X2))
    | ~ sP0(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),u1_pre_topc(X2))
    | sK5 != X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_295])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK7),X0,k2_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X0,u1_pre_topc(sK5))
    | r2_hidden(k9_subset_1(u1_struct_0(sK7),X0,k2_struct_0(sK7)),u1_pre_topc(sK7)) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_221,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_220,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_217,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_213,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_773,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_19,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_889,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1307,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK5) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_889])).

cnf(c_13,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_35,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1309,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK5) = X0
    | m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_889])).

cnf(c_1344,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK5) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1309])).

cnf(c_1571,plain,
    ( u1_struct_0(sK5) = X0
    | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1307,c_23,c_35,c_1344])).

cnf(c_1572,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK5) = X0 ),
    inference(renaming,[status(thm)],[c_1571])).

cnf(c_1578,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5) ),
    inference(equality_resolution,[status(thm)],[c_1572])).

cnf(c_2099,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(demodulation,[status(thm)],[c_1578,c_19])).

cnf(c_18,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1306,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK7) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_889])).

cnf(c_314,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_315,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_1308,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK7) = X0
    | m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_889])).

cnf(c_1341,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK7) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1308])).

cnf(c_1509,plain,
    ( u1_struct_0(sK7) = X0
    | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1306,c_315,c_1341])).

cnf(c_1510,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK7) = X0 ),
    inference(renaming,[status(thm)],[c_1509])).

cnf(c_1516,plain,
    ( u1_struct_0(sK8) = u1_struct_0(sK7) ),
    inference(equality_resolution,[status(thm)],[c_1510])).

cnf(c_1518,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK8) = X0 ),
    inference(demodulation,[status(thm)],[c_1516,c_1510])).

cnf(c_2123,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
    | u1_struct_0(sK6) = u1_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_2099,c_1518])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_890,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1468,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK5) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_890])).

cnf(c_24,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_34,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_36,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1470,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK5) = X1
    | m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_890])).

cnf(c_1745,plain,
    ( u1_pre_topc(sK5) = X1
    | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1468,c_24,c_36,c_1470])).

cnf(c_1746,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK5) = X1 ),
    inference(renaming,[status(thm)],[c_1745])).

cnf(c_1752,plain,
    ( u1_pre_topc(sK6) = u1_pre_topc(sK5) ),
    inference(equality_resolution,[status(thm)],[c_1746])).

cnf(c_1754,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK6) = X1 ),
    inference(demodulation,[status(thm)],[c_1752,c_1746])).

cnf(c_1467,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK7) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_890])).

cnf(c_316,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_1469,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK7) = X1
    | m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_890])).

cnf(c_1590,plain,
    ( u1_pre_topc(sK7) = X1
    | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1467,c_316,c_1469])).

cnf(c_1591,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK7) = X1 ),
    inference(renaming,[status(thm)],[c_1590])).

cnf(c_1597,plain,
    ( u1_pre_topc(sK8) = u1_pre_topc(sK7) ),
    inference(equality_resolution,[status(thm)],[c_1591])).

cnf(c_1599,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK8) = X1 ),
    inference(demodulation,[status(thm)],[c_1597,c_1591])).

cnf(c_1580,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK6) = X0 ),
    inference(demodulation,[status(thm)],[c_1578,c_1572])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_321,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_322,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_886,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_307,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_308,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_888,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_16,negated_conjecture,
    ( ~ m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_266,plain,
    ( sK5 != sK6
    | sK7 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:09:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.32/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/1.00  
% 2.32/1.00  ------  iProver source info
% 2.32/1.00  
% 2.32/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.32/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/1.00  git: non_committed_changes: false
% 2.32/1.00  git: last_make_outside_of_git: false
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     num_symb
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       true
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  ------ Parsing...
% 2.32/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/1.00  ------ Proving...
% 2.32/1.00  ------ Problem Properties 
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  clauses                                 9
% 2.32/1.00  conjectures                             2
% 2.32/1.00  EPR                                     1
% 2.32/1.00  Horn                                    9
% 2.32/1.00  unary                                   6
% 2.32/1.00  binary                                  1
% 2.32/1.00  lits                                    14
% 2.32/1.00  lits eq                                 8
% 2.32/1.00  fd_pure                                 0
% 2.32/1.00  fd_pseudo                               0
% 2.32/1.00  fd_cond                                 0
% 2.32/1.00  fd_pseudo_cond                          2
% 2.32/1.00  AC symbols                              0
% 2.32/1.00  
% 2.32/1.00  ------ Schedule dynamic 5 is on 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  Current options:
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     none
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       false
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ Proving...
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  % SZS output start Saturation for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  fof(f13,plain,(
% 2.32/1.00    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 2.32/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.32/1.00  
% 2.32/1.00  fof(f17,plain,(
% 2.32/1.00    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 2.32/1.00    inference(nnf_transformation,[],[f13])).
% 2.32/1.00  
% 2.32/1.00  fof(f18,plain,(
% 2.32/1.00    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 2.32/1.00    inference(flattening,[],[f17])).
% 2.32/1.00  
% 2.32/1.00  fof(f19,plain,(
% 2.32/1.00    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 2.32/1.00    inference(rectify,[],[f18])).
% 2.32/1.00  
% 2.32/1.00  fof(f22,plain,(
% 2.32/1.00    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f21,plain,(
% 2.32/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f20,plain,(
% 2.32/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f23,plain,(
% 2.32/1.00    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).
% 2.32/1.00  
% 2.32/1.00  fof(f34,plain,(
% 2.32/1.00    ( ! [X0,X5,X1] : (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f23])).
% 2.32/1.00  
% 2.32/1.00  fof(f1,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f8,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f1])).
% 2.32/1.00  
% 2.32/1.00  fof(f14,plain,(
% 2.32/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 2.32/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.32/1.00  
% 2.32/1.00  fof(f15,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(definition_folding,[],[f8,f14,f13])).
% 2.32/1.00  
% 2.32/1.00  fof(f41,plain,(
% 2.32/1.00    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f15])).
% 2.32/1.00  
% 2.32/1.00  fof(f16,plain,(
% 2.32/1.00    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 2.32/1.00    inference(nnf_transformation,[],[f14])).
% 2.32/1.00  
% 2.32/1.00  fof(f29,plain,(
% 2.32/1.00    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f16])).
% 2.32/1.00  
% 2.32/1.00  fof(f5,conjecture,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f6,negated_conjecture,(
% 2.32/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 2.32/1.00    inference(negated_conjecture,[],[f5])).
% 2.32/1.00  
% 2.32/1.00  fof(f11,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(X3,X1) & (m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X3)) & l1_pre_topc(X2)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f6])).
% 2.32/1.00  
% 2.32/1.00  fof(f12,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(X3,X1) & m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X3)) & l1_pre_topc(X2)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 2.32/1.00    inference(flattening,[],[f11])).
% 2.32/1.00  
% 2.32/1.00  fof(f27,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(X3,X1) & m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X3)) => (~m1_pre_topc(sK8,X1) & m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(sK8))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f26,plain,(
% 2.32/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(X3,X1) & m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X3)) & l1_pre_topc(X2)) => (? [X3] : (~m1_pre_topc(X3,X1) & m1_pre_topc(sK7,X0) & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X3)) & l1_pre_topc(sK7))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f25,plain,(
% 2.32/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(X3,X1) & m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X3)) & l1_pre_topc(X2)) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(X3,sK6) & m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(X3)) & l1_pre_topc(X2)) & l1_pre_topc(sK6))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f24,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(X3,X1) & m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X3)) & l1_pre_topc(X2)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(X3,X1) & m1_pre_topc(X2,sK5) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X3)) & l1_pre_topc(X2)) & l1_pre_topc(X1)) & l1_pre_topc(sK5))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f28,plain,(
% 2.32/1.00    (((~m1_pre_topc(sK8,sK6) & m1_pre_topc(sK7,sK5) & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) & l1_pre_topc(sK8)) & l1_pre_topc(sK7)) & l1_pre_topc(sK6)) & l1_pre_topc(sK5)),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f12,f27,f26,f25,f24])).
% 2.32/1.00  
% 2.32/1.00  fof(f51,plain,(
% 2.32/1.00    m1_pre_topc(sK7,sK5)),
% 2.32/1.00    inference(cnf_transformation,[],[f28])).
% 2.32/1.00  
% 2.32/1.00  fof(f45,plain,(
% 2.32/1.00    l1_pre_topc(sK5)),
% 2.32/1.00    inference(cnf_transformation,[],[f28])).
% 2.32/1.00  
% 2.32/1.00  fof(f47,plain,(
% 2.32/1.00    l1_pre_topc(sK7)),
% 2.32/1.00    inference(cnf_transformation,[],[f28])).
% 2.32/1.00  
% 2.32/1.00  fof(f33,plain,(
% 2.32/1.00    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f23])).
% 2.32/1.00  
% 2.32/1.00  fof(f32,plain,(
% 2.32/1.00    ( ! [X0,X5,X1] : (m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f23])).
% 2.32/1.00  
% 2.32/1.00  fof(f35,plain,(
% 2.32/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,u1_pre_topc(X0)) | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f23])).
% 2.32/1.00  
% 2.32/1.00  fof(f53,plain,(
% 2.32/1.00    ( ! [X6,X0,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0)) | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 2.32/1.00    inference(equality_resolution,[],[f35])).
% 2.32/1.00  
% 2.32/1.00  fof(f49,plain,(
% 2.32/1.00    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),
% 2.32/1.00    inference(cnf_transformation,[],[f28])).
% 2.32/1.00  
% 2.32/1.00  fof(f4,axiom,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f10,plain,(
% 2.32/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.32/1.00    inference(ennf_transformation,[],[f4])).
% 2.32/1.00  
% 2.32/1.00  fof(f43,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f10])).
% 2.32/1.00  
% 2.32/1.00  fof(f3,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f9,plain,(
% 2.32/1.01    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.32/1.01    inference(ennf_transformation,[],[f3])).
% 2.32/1.01  
% 2.32/1.01  fof(f42,plain,(
% 2.32/1.01    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f9])).
% 2.32/1.01  
% 2.32/1.01  fof(f50,plain,(
% 2.32/1.01    g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),
% 2.32/1.01    inference(cnf_transformation,[],[f28])).
% 2.32/1.01  
% 2.32/1.01  fof(f44,plain,(
% 2.32/1.01    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.32/1.01    inference(cnf_transformation,[],[f10])).
% 2.32/1.01  
% 2.32/1.01  fof(f46,plain,(
% 2.32/1.01    l1_pre_topc(sK6)),
% 2.32/1.01    inference(cnf_transformation,[],[f28])).
% 2.32/1.01  
% 2.32/1.01  fof(f48,plain,(
% 2.32/1.01    l1_pre_topc(sK8)),
% 2.32/1.01    inference(cnf_transformation,[],[f28])).
% 2.32/1.01  
% 2.32/1.01  fof(f52,plain,(
% 2.32/1.01    ~m1_pre_topc(sK8,sK6)),
% 2.32/1.01    inference(cnf_transformation,[],[f28])).
% 2.32/1.01  
% 2.32/1.01  cnf(c_8,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.32/1.01      | ~ sP0(X1,X2)
% 2.32/1.01      | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
% 2.32/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_12,plain,
% 2.32/1.01      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 2.32/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1,plain,
% 2.32/1.01      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 2.32/1.01      inference(cnf_transformation,[],[f29]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_17,negated_conjecture,
% 2.32/1.01      ( m1_pre_topc(sK7,sK5) ),
% 2.32/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_256,plain,
% 2.32/1.01      ( ~ sP1(X0,X1) | sP0(X1,X0) | sK5 != X0 | sK7 != X1 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_17]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_257,plain,
% 2.32/1.01      ( ~ sP1(sK5,sK7) | sP0(sK7,sK5) ),
% 2.32/1.01      inference(unflattening,[status(thm)],[c_256]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_292,plain,
% 2.32/1.01      ( sP0(sK7,sK5)
% 2.32/1.01      | ~ l1_pre_topc(X0)
% 2.32/1.01      | ~ l1_pre_topc(X1)
% 2.32/1.01      | sK5 != X0
% 2.32/1.01      | sK7 != X1 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_257]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_293,plain,
% 2.32/1.01      ( sP0(sK7,sK5) | ~ l1_pre_topc(sK5) | ~ l1_pre_topc(sK7) ),
% 2.32/1.01      inference(unflattening,[status(thm)],[c_292]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_23,negated_conjecture,
% 2.32/1.01      ( l1_pre_topc(sK5) ),
% 2.32/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_21,negated_conjecture,
% 2.32/1.01      ( l1_pre_topc(sK7) ),
% 2.32/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_295,plain,
% 2.32/1.01      ( sP0(sK7,sK5) ),
% 2.32/1.01      inference(global_propositional_subsumption,
% 2.32/1.01                [status(thm)],
% 2.32/1.01                [c_293,c_23,c_21]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_396,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.32/1.01      | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0
% 2.32/1.01      | sK5 != X2
% 2.32/1.01      | sK7 != X1 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_295]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_397,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(sK7))
% 2.32/1.01      | k9_subset_1(u1_struct_0(sK7),sK4(sK7,sK5,X0),k2_struct_0(sK7)) = X0 ),
% 2.32/1.01      inference(unflattening,[status(thm)],[c_396]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_9,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.32/1.01      | r2_hidden(sK4(X1,X2,X0),u1_pre_topc(X2))
% 2.32/1.01      | ~ sP0(X1,X2) ),
% 2.32/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_381,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.32/1.01      | r2_hidden(sK4(X1,X2,X0),u1_pre_topc(X2))
% 2.32/1.01      | sK5 != X2
% 2.32/1.01      | sK7 != X1 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_295]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_382,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(sK7))
% 2.32/1.01      | r2_hidden(sK4(sK7,sK5,X0),u1_pre_topc(sK5)) ),
% 2.32/1.01      inference(unflattening,[status(thm)],[c_381]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_10,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.01      | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.32/1.01      | ~ sP0(X1,X2) ),
% 2.32/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_366,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.01      | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.32/1.01      | sK5 != X2
% 2.32/1.01      | sK7 != X1 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_295]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_367,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 2.32/1.01      | m1_subset_1(sK4(sK7,sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(sK7)) ),
% 2.32/1.01      inference(unflattening,[status(thm)],[c_366]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_7,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.01      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.32/1.01      | r2_hidden(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),u1_pre_topc(X2))
% 2.32/1.01      | ~ sP0(X2,X1) ),
% 2.32/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_348,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.01      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.32/1.01      | r2_hidden(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),u1_pre_topc(X2))
% 2.32/1.01      | sK5 != X1
% 2.32/1.01      | sK7 != X2 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_295]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_349,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.32/1.01      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK7),X0,k2_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7)))
% 2.32/1.01      | ~ r2_hidden(X0,u1_pre_topc(sK5))
% 2.32/1.01      | r2_hidden(k9_subset_1(u1_struct_0(sK7),X0,k2_struct_0(sK7)),u1_pre_topc(sK7)) ),
% 2.32/1.01      inference(unflattening,[status(thm)],[c_348]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_221,plain,
% 2.32/1.01      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 2.32/1.01      theory(equality) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_220,plain,
% 2.32/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.32/1.01      theory(equality) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_217,plain,
% 2.32/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.32/1.01      theory(equality) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_213,plain,
% 2.32/1.01      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.32/1.01      theory(equality) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_773,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_19,negated_conjecture,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
% 2.32/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_15,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.32/1.01      | X2 = X1
% 2.32/1.01      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.32/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_889,plain,
% 2.32/1.01      ( X0 = X1
% 2.32/1.01      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.32/1.01      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.32/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1307,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_struct_0(sK5) = X0
% 2.32/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.32/1.01      inference(superposition,[status(thm)],[c_19,c_889]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_13,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.32/1.01      | ~ l1_pre_topc(X0) ),
% 2.32/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_35,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 2.32/1.01      | ~ l1_pre_topc(sK5) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1309,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_struct_0(sK5) = X0
% 2.32/1.01      | m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
% 2.32/1.01      inference(superposition,[status(thm)],[c_19,c_889]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1344,plain,
% 2.32/1.01      ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 2.32/1.01      | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_struct_0(sK5) = X0 ),
% 2.32/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1309]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1571,plain,
% 2.32/1.01      ( u1_struct_0(sK5) = X0
% 2.32/1.01      | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1) ),
% 2.32/1.01      inference(global_propositional_subsumption,
% 2.32/1.01                [status(thm)],
% 2.32/1.01                [c_1307,c_23,c_35,c_1344]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1572,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_struct_0(sK5) = X0 ),
% 2.32/1.01      inference(renaming,[status(thm)],[c_1571]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1578,plain,
% 2.32/1.01      ( u1_struct_0(sK6) = u1_struct_0(sK5) ),
% 2.32/1.01      inference(equality_resolution,[status(thm)],[c_1572]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_2099,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
% 2.32/1.01      inference(demodulation,[status(thm)],[c_1578,c_19]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_18,negated_conjecture,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
% 2.32/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1306,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_struct_0(sK7) = X0
% 2.32/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.32/1.01      inference(superposition,[status(thm)],[c_18,c_889]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_314,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.32/1.01      | sK7 != X0 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_315,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
% 2.32/1.01      inference(unflattening,[status(thm)],[c_314]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1308,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_struct_0(sK7) = X0
% 2.32/1.01      | m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
% 2.32/1.01      inference(superposition,[status(thm)],[c_18,c_889]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1341,plain,
% 2.32/1.01      ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 2.32/1.01      | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_struct_0(sK7) = X0 ),
% 2.32/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1308]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1509,plain,
% 2.32/1.01      ( u1_struct_0(sK7) = X0
% 2.32/1.01      | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1) ),
% 2.32/1.01      inference(global_propositional_subsumption,
% 2.32/1.01                [status(thm)],
% 2.32/1.01                [c_1306,c_315,c_1341]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1510,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_struct_0(sK7) = X0 ),
% 2.32/1.01      inference(renaming,[status(thm)],[c_1509]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1516,plain,
% 2.32/1.01      ( u1_struct_0(sK8) = u1_struct_0(sK7) ),
% 2.32/1.01      inference(equality_resolution,[status(thm)],[c_1510]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1518,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_struct_0(sK8) = X0 ),
% 2.32/1.01      inference(demodulation,[status(thm)],[c_1516,c_1510]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_2123,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
% 2.32/1.01      | u1_struct_0(sK6) = u1_struct_0(sK8) ),
% 2.32/1.01      inference(superposition,[status(thm)],[c_2099,c_1518]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_14,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.32/1.01      | X2 = X0
% 2.32/1.01      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 2.32/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_890,plain,
% 2.32/1.01      ( X0 = X1
% 2.32/1.01      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 2.32/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 2.32/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1468,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_pre_topc(sK5) = X1
% 2.32/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.32/1.01      inference(superposition,[status(thm)],[c_19,c_890]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_24,plain,
% 2.32/1.01      ( l1_pre_topc(sK5) = iProver_top ),
% 2.32/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_34,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.32/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.32/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_36,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
% 2.32/1.01      | l1_pre_topc(sK5) != iProver_top ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_34]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1470,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_pre_topc(sK5) = X1
% 2.32/1.01      | m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
% 2.32/1.01      inference(superposition,[status(thm)],[c_19,c_890]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1745,plain,
% 2.32/1.01      ( u1_pre_topc(sK5) = X1
% 2.32/1.01      | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1) ),
% 2.32/1.01      inference(global_propositional_subsumption,
% 2.32/1.01                [status(thm)],
% 2.32/1.01                [c_1468,c_24,c_36,c_1470]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1746,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_pre_topc(sK5) = X1 ),
% 2.32/1.01      inference(renaming,[status(thm)],[c_1745]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1752,plain,
% 2.32/1.01      ( u1_pre_topc(sK6) = u1_pre_topc(sK5) ),
% 2.32/1.01      inference(equality_resolution,[status(thm)],[c_1746]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1754,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_pre_topc(sK6) = X1 ),
% 2.32/1.01      inference(demodulation,[status(thm)],[c_1752,c_1746]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1467,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_pre_topc(sK7) = X1
% 2.32/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.32/1.01      inference(superposition,[status(thm)],[c_18,c_890]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_316,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
% 2.32/1.01      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1469,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_pre_topc(sK7) = X1
% 2.32/1.01      | m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
% 2.32/1.01      inference(superposition,[status(thm)],[c_18,c_890]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1590,plain,
% 2.32/1.01      ( u1_pre_topc(sK7) = X1
% 2.32/1.01      | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1) ),
% 2.32/1.01      inference(global_propositional_subsumption,
% 2.32/1.01                [status(thm)],
% 2.32/1.01                [c_1467,c_316,c_1469]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1591,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_pre_topc(sK7) = X1 ),
% 2.32/1.01      inference(renaming,[status(thm)],[c_1590]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1597,plain,
% 2.32/1.01      ( u1_pre_topc(sK8) = u1_pre_topc(sK7) ),
% 2.32/1.01      inference(equality_resolution,[status(thm)],[c_1591]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1599,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_pre_topc(sK8) = X1 ),
% 2.32/1.01      inference(demodulation,[status(thm)],[c_1597,c_1591]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1580,plain,
% 2.32/1.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
% 2.32/1.01      | u1_struct_0(sK6) = X0 ),
% 2.32/1.01      inference(demodulation,[status(thm)],[c_1578,c_1572]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_22,negated_conjecture,
% 2.32/1.01      ( l1_pre_topc(sK6) ),
% 2.32/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_321,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.32/1.01      | sK6 != X0 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_322,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
% 2.32/1.01      inference(unflattening,[status(thm)],[c_321]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_886,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top ),
% 2.32/1.01      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_20,negated_conjecture,
% 2.32/1.01      ( l1_pre_topc(sK8) ),
% 2.32/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_307,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.32/1.01      | sK8 != X0 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_308,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
% 2.32/1.01      inference(unflattening,[status(thm)],[c_307]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_888,plain,
% 2.32/1.01      ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
% 2.32/1.01      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_16,negated_conjecture,
% 2.32/1.01      ( ~ m1_pre_topc(sK8,sK6) ),
% 2.32/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_266,plain,
% 2.32/1.01      ( sK5 != sK6 | sK7 != sK8 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_17]) ).
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  % SZS output end Saturation for theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  ------                               Statistics
% 2.32/1.01  
% 2.32/1.01  ------ General
% 2.32/1.01  
% 2.32/1.01  abstr_ref_over_cycles:                  0
% 2.32/1.01  abstr_ref_under_cycles:                 0
% 2.32/1.01  gc_basic_clause_elim:                   0
% 2.32/1.01  forced_gc_time:                         0
% 2.32/1.01  parsing_time:                           0.009
% 2.32/1.01  unif_index_cands_time:                  0.
% 2.32/1.01  unif_index_add_time:                    0.
% 2.32/1.01  orderings_time:                         0.
% 2.32/1.01  out_proof_time:                         0.
% 2.32/1.01  total_time:                             0.115
% 2.32/1.01  num_of_symbols:                         51
% 2.32/1.01  num_of_terms:                           2936
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing
% 2.32/1.01  
% 2.32/1.01  num_of_splits:                          0
% 2.32/1.01  num_of_split_atoms:                     0
% 2.32/1.01  num_of_reused_defs:                     0
% 2.32/1.01  num_eq_ax_congr_red:                    13
% 2.32/1.01  num_of_sem_filtered_clauses:            5
% 2.32/1.01  num_of_subtypes:                        0
% 2.32/1.01  monotx_restored_types:                  0
% 2.32/1.01  sat_num_of_epr_types:                   0
% 2.32/1.01  sat_num_of_non_cyclic_types:            0
% 2.32/1.01  sat_guarded_non_collapsed_types:        0
% 2.32/1.01  num_pure_diseq_elim:                    0
% 2.32/1.01  simp_replaced_by:                       0
% 2.32/1.01  res_preprocessed:                       79
% 2.32/1.01  prep_upred:                             0
% 2.32/1.01  prep_unflattend:                        36
% 2.32/1.01  smt_new_axioms:                         0
% 2.32/1.01  pred_elim_cands:                        1
% 2.32/1.01  pred_elim:                              5
% 2.32/1.01  pred_elim_cl:                           11
% 2.32/1.01  pred_elim_cycles:                       8
% 2.32/1.01  merged_defs:                            0
% 2.32/1.01  merged_defs_ncl:                        0
% 2.32/1.01  bin_hyper_res:                          0
% 2.32/1.01  prep_cycles:                            5
% 2.32/1.01  pred_elim_time:                         0.007
% 2.32/1.01  splitting_time:                         0.
% 2.32/1.01  sem_filter_time:                        0.
% 2.32/1.01  monotx_time:                            0.
% 2.32/1.01  subtype_inf_time:                       0.
% 2.32/1.01  
% 2.32/1.01  ------ Problem properties
% 2.32/1.01  
% 2.32/1.01  clauses:                                9
% 2.32/1.01  conjectures:                            2
% 2.32/1.01  epr:                                    1
% 2.32/1.01  horn:                                   9
% 2.32/1.01  ground:                                 7
% 2.32/1.01  unary:                                  6
% 2.32/1.01  binary:                                 1
% 2.32/1.01  lits:                                   14
% 2.32/1.01  lits_eq:                                8
% 2.32/1.01  fd_pure:                                0
% 2.32/1.01  fd_pseudo:                              0
% 2.32/1.01  fd_cond:                                0
% 2.32/1.01  fd_pseudo_cond:                         2
% 2.32/1.01  ac_symbols:                             0
% 2.32/1.01  
% 2.32/1.01  ------ Propositional Solver
% 2.32/1.01  
% 2.32/1.01  prop_solver_calls:                      30
% 2.32/1.01  prop_fast_solver_calls:                 485
% 2.32/1.01  smt_solver_calls:                       0
% 2.32/1.01  smt_fast_solver_calls:                  0
% 2.32/1.01  prop_num_of_clauses:                    940
% 2.32/1.01  prop_preprocess_simplified:             2956
% 2.32/1.01  prop_fo_subsumed:                       10
% 2.32/1.01  prop_solver_time:                       0.
% 2.32/1.01  smt_solver_time:                        0.
% 2.32/1.01  smt_fast_solver_time:                   0.
% 2.32/1.01  prop_fast_solver_time:                  0.
% 2.32/1.01  prop_unsat_core_time:                   0.
% 2.32/1.01  
% 2.32/1.01  ------ QBF
% 2.32/1.01  
% 2.32/1.01  qbf_q_res:                              0
% 2.32/1.01  qbf_num_tautologies:                    0
% 2.32/1.01  qbf_prep_cycles:                        0
% 2.32/1.01  
% 2.32/1.01  ------ BMC1
% 2.32/1.01  
% 2.32/1.01  bmc1_current_bound:                     -1
% 2.32/1.01  bmc1_last_solved_bound:                 -1
% 2.32/1.01  bmc1_unsat_core_size:                   -1
% 2.32/1.01  bmc1_unsat_core_parents_size:           -1
% 2.32/1.01  bmc1_merge_next_fun:                    0
% 2.32/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.32/1.01  
% 2.32/1.01  ------ Instantiation
% 2.32/1.01  
% 2.32/1.01  inst_num_of_clauses:                    291
% 2.32/1.01  inst_num_in_passive:                    46
% 2.32/1.01  inst_num_in_active:                     129
% 2.32/1.01  inst_num_in_unprocessed:                116
% 2.32/1.01  inst_num_of_loops:                      130
% 2.32/1.01  inst_num_of_learning_restarts:          0
% 2.32/1.01  inst_num_moves_active_passive:          0
% 2.32/1.01  inst_lit_activity:                      0
% 2.32/1.01  inst_lit_activity_moves:                0
% 2.32/1.01  inst_num_tautologies:                   0
% 2.32/1.01  inst_num_prop_implied:                  0
% 2.32/1.01  inst_num_existing_simplified:           0
% 2.32/1.01  inst_num_eq_res_simplified:             0
% 2.32/1.01  inst_num_child_elim:                    0
% 2.32/1.01  inst_num_of_dismatching_blockings:      83
% 2.32/1.01  inst_num_of_non_proper_insts:           318
% 2.32/1.01  inst_num_of_duplicates:                 0
% 2.32/1.01  inst_inst_num_from_inst_to_res:         0
% 2.32/1.01  inst_dismatching_checking_time:         0.
% 2.32/1.01  
% 2.32/1.01  ------ Resolution
% 2.32/1.01  
% 2.32/1.01  res_num_of_clauses:                     0
% 2.32/1.01  res_num_in_passive:                     0
% 2.32/1.01  res_num_in_active:                      0
% 2.32/1.01  res_num_of_loops:                       84
% 2.32/1.01  res_forward_subset_subsumed:            33
% 2.32/1.01  res_backward_subset_subsumed:           0
% 2.32/1.01  res_forward_subsumed:                   0
% 2.32/1.01  res_backward_subsumed:                  0
% 2.32/1.01  res_forward_subsumption_resolution:     0
% 2.32/1.01  res_backward_subsumption_resolution:    0
% 2.32/1.01  res_clause_to_clause_subsumption:       82
% 2.32/1.01  res_orphan_elimination:                 0
% 2.32/1.01  res_tautology_del:                      35
% 2.32/1.01  res_num_eq_res_simplified:              0
% 2.32/1.01  res_num_sel_changes:                    0
% 2.32/1.01  res_moves_from_active_to_pass:          0
% 2.32/1.01  
% 2.32/1.01  ------ Superposition
% 2.32/1.01  
% 2.32/1.01  sup_time_total:                         0.
% 2.32/1.01  sup_time_generating:                    0.
% 2.32/1.01  sup_time_sim_full:                      0.
% 2.32/1.01  sup_time_sim_immed:                     0.
% 2.32/1.01  
% 2.32/1.01  sup_num_of_clauses:                     23
% 2.32/1.01  sup_num_in_active:                      14
% 2.32/1.01  sup_num_in_passive:                     9
% 2.32/1.01  sup_num_of_loops:                       25
% 2.32/1.01  sup_fw_superposition:                   17
% 2.32/1.01  sup_bw_superposition:                   9
% 2.32/1.01  sup_immediate_simplified:               5
% 2.32/1.01  sup_given_eliminated:                   4
% 2.32/1.01  comparisons_done:                       0
% 2.32/1.01  comparisons_avoided:                    0
% 2.32/1.01  
% 2.32/1.01  ------ Simplifications
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  sim_fw_subset_subsumed:                 4
% 2.32/1.01  sim_bw_subset_subsumed:                 4
% 2.32/1.01  sim_fw_subsumed:                        1
% 2.32/1.01  sim_bw_subsumed:                        0
% 2.32/1.01  sim_fw_subsumption_res:                 0
% 2.32/1.01  sim_bw_subsumption_res:                 0
% 2.32/1.01  sim_tautology_del:                      0
% 2.32/1.01  sim_eq_tautology_del:                   12
% 2.32/1.01  sim_eq_res_simp:                        0
% 2.32/1.01  sim_fw_demodulated:                     2
% 2.32/1.01  sim_bw_demodulated:                     11
% 2.32/1.01  sim_light_normalised:                   3
% 2.32/1.01  sim_joinable_taut:                      0
% 2.32/1.01  sim_joinable_simp:                      0
% 2.32/1.01  sim_ac_normalised:                      0
% 2.32/1.01  sim_smt_subsumption:                    0
% 2.32/1.01  
%------------------------------------------------------------------------------
