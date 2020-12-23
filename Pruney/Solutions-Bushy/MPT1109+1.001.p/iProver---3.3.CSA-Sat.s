%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1109+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:54 EST 2020

% Result     : CounterSatisfiable 2.85s
% Output     : Saturation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  154 (3181 expanded)
%              Number of clauses        :  101 ( 918 expanded)
%              Number of leaves         :   21 (1017 expanded)
%              Depth                    :   15
%              Number of atoms          :  547 (17864 expanded)
%              Number of equality atoms :  199 (5511 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
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

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f10,f18,f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f32,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    & m1_pre_topc(sK7,sK5)
    & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
    & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    & l1_pre_topc(sK8)
    & l1_pre_topc(sK7)
    & l1_pre_topc(sK6)
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f16,f31,f30,f29,f28])).

fof(f58,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f56,plain,(
    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ~ m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2)
    | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_292,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_13,c_2])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_296,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_15])).

cnf(c_297,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_349,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_297,c_20])).

cnf(c_350,plain,
    ( sP0(sK7,sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_352,plain,
    ( sP0(sK7,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_26])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0
    | sK5 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_352])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X0,u1_pre_topc(sK7))
    | k9_subset_1(u1_struct_0(sK7),sK4(sK7,sK5,X0),k2_struct_0(sK7)) = X0 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(sK4(X1,X2,X0),u1_pre_topc(X2))
    | ~ sP0(X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(sK4(X1,X2,X0),u1_pre_topc(X2))
    | sK5 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_352])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X0,u1_pre_topc(sK7))
    | r2_hidden(sK4(sK7,sK5,X0),u1_pre_topc(sK5)) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | sK5 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_352])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK4(sK7,sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,u1_pre_topc(sK7)) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),u1_pre_topc(X2))
    | ~ sP0(X2,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),u1_pre_topc(X2))
    | sK5 != X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_352])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK7),X0,k2_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X0,u1_pre_topc(sK5))
    | r2_hidden(k9_subset_1(u1_struct_0(sK7),X0,k2_struct_0(sK7)),u1_pre_topc(sK7)) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_251,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_250,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_247,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_244,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_866,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_14,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_278,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_14,c_0])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_399,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_278,c_25])).

cnf(c_400,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_411,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_278,c_26])).

cnf(c_412,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_1010,plain,
    ( g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(light_normalisation,[status(thm)],[c_22,c_400,c_412])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_985,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1490,plain,
    ( g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK5) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_985])).

cnf(c_16,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_416,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_417,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_980,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_994,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK5)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_980,c_412])).

cnf(c_1492,plain,
    ( g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK5) = X1
    | m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_985])).

cnf(c_1745,plain,
    ( u1_pre_topc(sK5) = X1
    | g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1490,c_994,c_1492])).

cnf(c_1746,plain,
    ( g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK5) = X1 ),
    inference(renaming,[status(thm)],[c_1745])).

cnf(c_1752,plain,
    ( u1_pre_topc(sK6) = u1_pre_topc(sK5) ),
    inference(equality_resolution,[status(thm)],[c_1746])).

cnf(c_21,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_375,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_278,c_23])).

cnf(c_376,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_387,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_278,c_24])).

cnf(c_388,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_1013,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(k2_struct_0(sK7),u1_pre_topc(sK7)) ),
    inference(light_normalisation,[status(thm)],[c_21,c_376,c_388])).

cnf(c_1751,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6))
    | u1_pre_topc(sK5) = u1_pre_topc(sK7) ),
    inference(superposition,[status(thm)],[c_1013,c_1746])).

cnf(c_2401,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6))
    | u1_pre_topc(sK6) = u1_pre_topc(sK7) ),
    inference(demodulation,[status(thm)],[c_1752,c_1751])).

cnf(c_1491,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK7) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1013,c_985])).

cnf(c_392,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_393,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_982,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_1000,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK7)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_982,c_388])).

cnf(c_1493,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK7) = X1
    | m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1013,c_985])).

cnf(c_2156,plain,
    ( u1_pre_topc(sK7) = X1
    | g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1491,c_1000,c_1493])).

cnf(c_2157,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK7) = X1 ),
    inference(renaming,[status(thm)],[c_2156])).

cnf(c_2163,plain,
    ( u1_pre_topc(sK8) = u1_pre_topc(sK7) ),
    inference(equality_resolution,[status(thm)],[c_2157])).

cnf(c_2564,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6))
    | u1_pre_topc(sK6) = u1_pre_topc(sK8) ),
    inference(light_normalisation,[status(thm)],[c_2401,c_2163])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_984,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1445,plain,
    ( g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | k2_struct_0(sK5) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_984])).

cnf(c_1447,plain,
    ( g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | k2_struct_0(sK5) = X0
    | m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_984])).

cnf(c_1654,plain,
    ( k2_struct_0(sK5) = X0
    | g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1445,c_994,c_1447])).

cnf(c_1655,plain,
    ( g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | k2_struct_0(sK5) = X0 ),
    inference(renaming,[status(thm)],[c_1654])).

cnf(c_1661,plain,
    ( k2_struct_0(sK6) = k2_struct_0(sK5) ),
    inference(equality_resolution,[status(thm)],[c_1655])).

cnf(c_1446,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | k2_struct_0(sK7) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1013,c_984])).

cnf(c_1448,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | k2_struct_0(sK7) = X0
    | m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1013,c_984])).

cnf(c_1673,plain,
    ( k2_struct_0(sK7) = X0
    | g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1446,c_1000,c_1448])).

cnf(c_1674,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | k2_struct_0(sK7) = X0 ),
    inference(renaming,[status(thm)],[c_1673])).

cnf(c_1678,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6))
    | k2_struct_0(sK7) = k2_struct_0(sK5) ),
    inference(superposition,[status(thm)],[c_1010,c_1674])).

cnf(c_2175,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6))
    | k2_struct_0(sK6) = k2_struct_0(sK7) ),
    inference(demodulation,[status(thm)],[c_1661,c_1678])).

cnf(c_1680,plain,
    ( k2_struct_0(sK7) = k2_struct_0(sK8) ),
    inference(equality_resolution,[status(thm)],[c_1674])).

cnf(c_2561,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6))
    | k2_struct_0(sK6) = k2_struct_0(sK8) ),
    inference(light_normalisation,[status(thm)],[c_2175,c_1680])).

cnf(c_2305,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK8) ),
    inference(demodulation,[status(thm)],[c_1680,c_388])).

cnf(c_2178,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK6) ),
    inference(demodulation,[status(thm)],[c_1661,c_412])).

cnf(c_2165,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK8) = X1 ),
    inference(demodulation,[status(thm)],[c_2163,c_2157])).

cnf(c_1754,plain,
    ( g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK6) = X1 ),
    inference(demodulation,[status(thm)],[c_1752,c_1746])).

cnf(c_1682,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X0,X1)
    | k2_struct_0(sK8) = X0 ),
    inference(demodulation,[status(thm)],[c_1680,c_1674])).

cnf(c_1663,plain,
    ( g1_pre_topc(k2_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | k2_struct_0(sK6) = X0 ),
    inference(demodulation,[status(thm)],[c_1661,c_1655])).

cnf(c_380,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_381,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_983,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_1003,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK8)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_983,c_376])).

cnf(c_404,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_405,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_981,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_997,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK6)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_981,c_400])).

cnf(c_19,negated_conjecture,
    ( ~ m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_362,plain,
    ( sK5 != sK6
    | sK7 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_20])).


%------------------------------------------------------------------------------
