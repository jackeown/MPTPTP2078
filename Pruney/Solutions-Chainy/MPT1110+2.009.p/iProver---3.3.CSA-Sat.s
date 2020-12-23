%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:27 EST 2020

% Result     : CounterSatisfiable 3.68s
% Output     : Saturation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 876 expanded)
%              Number of clauses        :  114 ( 265 expanded)
%              Number of leaves         :   14 ( 224 expanded)
%              Depth                    :   14
%              Number of atoms          :  728 (5235 expanded)
%              Number of equality atoms :  331 ( 991 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(f16,plain,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

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
    inference(nnf_transformation,[],[f13])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK3(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = sK3(X0,X1)
              & r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) )
        & m1_pre_topc(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,sK6) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    & m1_pre_topc(sK7,sK6)
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f12,f31,f30,f29])).

fof(f54,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f32])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = sK3(X0,X1)
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    m1_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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
    inference(definition_folding,[],[f10,f14,f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_249,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1851,plain,
    ( r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1852,plain,
    ( r2_hidden(sK2(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2534,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1851,c_1852])).

cnf(c_10,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1321,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ iProver_ARSWP_67
    | arAF0_sP0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_1837,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | iProver_ARSWP_67 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_2450,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_3271,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
    | ~ iProver_ARSWP_67
    | arAF0_sP0_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2450,c_1321])).

cnf(c_3280,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | iProver_ARSWP_67 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3271])).

cnf(c_5083,plain,
    ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | iProver_ARSWP_67 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1837,c_3280])).

cnf(c_5084,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | iProver_ARSWP_67 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(renaming,[status(thm)],[c_5083])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1848,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5091,plain,
    ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(arAF0_sK4_0,u1_struct_0(X0)) = iProver_top
    | iProver_ARSWP_67 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5084,c_1848])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1850,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2626,plain,
    ( r2_hidden(sK2(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1851,c_1850])).

cnf(c_3220,plain,
    ( r2_hidden(sK2(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2626,c_1850])).

cnf(c_5114,plain,
    ( r2_hidden(sK2(arAF0_sK4_0,X0),X1) = iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(u1_struct_0(X2),X1) != iProver_top
    | r1_tarski(arAF0_sK4_0,X0) = iProver_top
    | iProver_ARSWP_67 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5091,c_3220])).

cnf(c_5791,plain,
    ( r2_hidden(sK2(arAF0_sK4_0,X0),u1_struct_0(X1)) = iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(arAF0_sK4_0,X0) = iProver_top
    | iProver_ARSWP_67 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_5114])).

cnf(c_11,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1322,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ iProver_ARSWP_68
    | arAF0_sP0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_1836,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | iProver_ARSWP_68 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_3272,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ iProver_ARSWP_68
    | arAF0_sP0_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2450,c_1322])).

cnf(c_3277,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | iProver_ARSWP_68 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3272])).

cnf(c_3385,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | iProver_ARSWP_68 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1836,c_3277])).

cnf(c_3392,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | iProver_ARSWP_68 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3385,c_1848])).

cnf(c_4927,plain,
    ( r2_hidden(sK2(arAF0_sK3_0,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(X2),X1) != iProver_top
    | r1_tarski(arAF0_sK3_0,X0) = iProver_top
    | iProver_ARSWP_68 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3392,c_3220])).

cnf(c_5634,plain,
    ( r2_hidden(sK2(arAF0_sK3_0,X0),u1_struct_0(X1)) = iProver_top
    | r1_tarski(arAF0_sK3_0,X0) = iProver_top
    | iProver_ARSWP_68 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_4927])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1846,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(arAF0_sK5_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
    | ~ iProver_ARSWP_72
    | ~ arAF0_sP0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_15])).

cnf(c_1832,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(arAF0_sK5_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_72 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_2410,plain,
    ( m1_subset_1(arAF0_sK5_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_72 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_1832])).

cnf(c_2714,plain,
    ( r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
    | r1_tarski(arAF0_sK5_0,u1_struct_0(X0)) = iProver_top
    | iProver_ARSWP_72 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_2410,c_1848])).

cnf(c_4928,plain,
    ( r2_hidden(sK2(arAF0_sK5_0,X0),X1) = iProver_top
    | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
    | r1_tarski(u1_struct_0(X2),X1) != iProver_top
    | r1_tarski(arAF0_sK5_0,X0) = iProver_top
    | iProver_ARSWP_72 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_2714,c_3220])).

cnf(c_5519,plain,
    ( r2_hidden(sK2(arAF0_sK5_0,X0),u1_struct_0(X1)) = iProver_top
    | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
    | r1_tarski(arAF0_sK5_0,X0) = iProver_top
    | iProver_ARSWP_72 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_4928])).

cnf(c_2295,plain,
    ( r1_tarski(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_1848])).

cnf(c_4925,plain,
    ( r2_hidden(sK2(sK8,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK7),X1) != iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2295,c_3220])).

cnf(c_5248,plain,
    ( r2_hidden(sK2(sK8,X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(u1_struct_0(sK7),X2) != iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4925,c_1850])).

cnf(c_5247,plain,
    ( r1_tarski(u1_struct_0(sK7),X0) != iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4925,c_1852])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1849,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
    | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0)
    | ~ iProver_ARSWP_69
    | ~ arAF0_sP0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_1835,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
    | iProver_ARSWP_69 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_4025,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
    | iProver_ARSWP_69 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1835])).

cnf(c_4675,plain,
    ( r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X2)) != iProver_top
    | iProver_ARSWP_69 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_4025])).

cnf(c_4787,plain,
    ( r2_hidden(u1_struct_0(X0),arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X1)) != iProver_top
    | iProver_ARSWP_69 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_4675])).

cnf(c_4026,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
    | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_69 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_1835])).

cnf(c_4499,plain,
    ( r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
    | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
    | r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) != iProver_top
    | iProver_ARSWP_69 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_4026])).

cnf(c_9,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1320,plain,
    ( r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0)
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ iProver_ARSWP_66
    | arAF0_sP0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_1838,plain,
    ( r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0) = iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | iProver_ARSWP_66 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1320])).

cnf(c_3273,plain,
    ( r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0)
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
    | ~ iProver_ARSWP_66
    | arAF0_sP0_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2450,c_1320])).

cnf(c_3276,plain,
    ( r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0) = iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | iProver_ARSWP_66 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3273])).

cnf(c_4381,plain,
    ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0) = iProver_top
    | iProver_ARSWP_66 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1838,c_3276])).

cnf(c_4382,plain,
    ( r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0) = iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | iProver_ARSWP_66 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(renaming,[status(thm)],[c_4381])).

cnf(c_4389,plain,
    ( r2_hidden(arAF0_sK4_0,X0) = iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(arAF0_u1_pre_topc_0,X0) != iProver_top
    | iProver_ARSWP_66 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4382,c_1850])).

cnf(c_8,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = sK3(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1319,plain,
    ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ iProver_ARSWP_65
    | arAF0_sP0_0
    | arAF0_k9_subset_1_0 = arAF0_sK3_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_1839,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK3_0
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_3274,plain,
    ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
    | ~ iProver_ARSWP_65
    | arAF0_sP0_0
    | arAF0_k9_subset_1_0 = arAF0_sK3_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2450,c_1319])).

cnf(c_3275,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK3_0
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | iProver_ARSWP_65 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3274])).

cnf(c_4200,plain,
    ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | arAF0_k9_subset_1_0 = arAF0_sK3_0
    | iProver_ARSWP_65 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1839,c_3275])).

cnf(c_4201,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK3_0
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
    | iProver_ARSWP_65 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(renaming,[status(thm)],[c_4200])).

cnf(c_4208,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK3_0
    | r2_hidden(arAF0_sK3_0,X0) = iProver_top
    | r1_tarski(arAF0_u1_pre_topc_0,X0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4201,c_1850])).

cnf(c_2419,plain,
    ( m1_subset_1(arAF0_sK5_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r2_hidden(X1,arAF0_u1_pre_topc_0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
    | iProver_ARSWP_72 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1832])).

cnf(c_4005,plain,
    ( m1_subset_1(arAF0_sK5_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r2_hidden(u1_struct_0(X1),arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_72 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_2419])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,u1_pre_topc(X0))
    | r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
    | r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0)
    | ~ iProver_ARSWP_71
    | ~ arAF0_sP0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_14])).

cnf(c_1833,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0) = iProver_top
    | iProver_ARSWP_71 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1325])).

cnf(c_3077,plain,
    ( r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0) = iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | iProver_ARSWP_71 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1833])).

cnf(c_3841,plain,
    ( r2_hidden(u1_struct_0(X0),arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0) = iProver_top
    | iProver_ARSWP_71 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_3077])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,u1_pre_topc(X0))
    | k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2),k2_struct_0(X0)) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
    | ~ iProver_ARSWP_70
    | ~ arAF0_sP0_0
    | arAF0_k9_subset_1_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_13])).

cnf(c_1834,plain,
    ( arAF0_k9_subset_1_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_70 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_3410,plain,
    ( arAF0_k9_subset_1_0 = X0
    | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | iProver_ARSWP_70 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1834])).

cnf(c_3669,plain,
    ( u1_struct_0(X0) = arAF0_k9_subset_1_0
    | r2_hidden(u1_struct_0(X0),arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_70 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_3410])).

cnf(c_3413,plain,
    ( arAF0_sK5_0 = arAF0_k9_subset_1_0
    | r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_72 != iProver_top
    | iProver_ARSWP_70 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_2410,c_1834])).

cnf(c_3411,plain,
    ( arAF0_k9_subset_1_0 = sK8
    | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_70 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_1834])).

cnf(c_7,plain,
    ( sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)) != sK3(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1318,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
    | ~ r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ iProver_ARSWP_64
    | arAF0_sP0_0
    | arAF0_k9_subset_1_0 != arAF0_sK3_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_1840,plain,
    ( arAF0_k9_subset_1_0 != arAF0_sK3_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) != iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | iProver_ARSWP_64 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_3270,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
    | ~ r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
    | ~ iProver_ARSWP_64
    | arAF0_sP0_0
    | arAF0_k9_subset_1_0 != arAF0_sK3_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2450,c_1318])).

cnf(c_3283,plain,
    ( arAF0_k9_subset_1_0 != arAF0_sK3_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_64 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3270])).

cnf(c_4910,plain,
    ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | arAF0_k9_subset_1_0 != arAF0_sK3_0
    | iProver_ARSWP_64 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1840,c_3283])).

cnf(c_4911,plain,
    ( arAF0_k9_subset_1_0 != arAF0_sK3_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
    | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_64 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(renaming,[status(thm)],[c_4910])).

cnf(c_3078,plain,
    ( r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0) = iProver_top
    | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
    | iProver_ARSWP_71 != iProver_top
    | arAF0_sP0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_1833])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1330,negated_conjecture,
    ( ~ iProver_ARSWP_76
    | arAF0_m1_pre_topc_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_21])).

cnf(c_1829,plain,
    ( iProver_ARSWP_76 != iProver_top
    | arAF0_m1_pre_topc_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1331,negated_conjecture,
    ( ~ iProver_ARSWP_77
    | arAF0_l1_pre_topc_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_22])).

cnf(c_1828,plain,
    ( iProver_ARSWP_77 != iProver_top
    | arAF0_l1_pre_topc_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1331])).

cnf(c_17,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1328,plain,
    ( ~ iProver_ARSWP_74
    | ~ arAF0_l1_pre_topc_0
    | arAF0_sP1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_17])).

cnf(c_1830,plain,
    ( iProver_ARSWP_74 != iProver_top
    | arAF0_l1_pre_topc_0 != iProver_top
    | arAF0_sP1_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_2219,plain,
    ( iProver_ARSWP_77 != iProver_top
    | iProver_ARSWP_74 != iProver_top
    | arAF0_sP1_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_1828,c_1830])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1317,plain,
    ( ~ iProver_ARSWP_63
    | ~ arAF0_m1_pre_topc_0
    | arAF0_sP0_0
    | ~ arAF0_sP1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_1841,plain,
    ( iProver_ARSWP_63 != iProver_top
    | arAF0_m1_pre_topc_0 != iProver_top
    | arAF0_sP0_0 = iProver_top
    | arAF0_sP1_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1317])).

cnf(c_2829,plain,
    ( iProver_ARSWP_77 != iProver_top
    | iProver_ARSWP_74 != iProver_top
    | iProver_ARSWP_63 != iProver_top
    | arAF0_m1_pre_topc_0 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_1841])).

cnf(c_2953,plain,
    ( iProver_ARSWP_77 != iProver_top
    | iProver_ARSWP_76 != iProver_top
    | iProver_ARSWP_74 != iProver_top
    | iProver_ARSWP_63 != iProver_top
    | arAF0_sP0_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_1829,c_2829])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1847,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2418,plain,
    ( r1_tarski(sK8,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1847])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1316,plain,
    ( ~ iProver_ARSWP_62
    | arAF0_m1_pre_topc_0
    | ~ arAF0_sP0_0
    | ~ arAF0_sP1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_1842,plain,
    ( iProver_ARSWP_62 != iProver_top
    | arAF0_m1_pre_topc_0 = iProver_top
    | arAF0_sP0_0 != iProver_top
    | arAF0_sP1_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.68/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.99  
% 3.68/0.99  ------  iProver source info
% 3.68/0.99  
% 3.68/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.99  git: non_committed_changes: false
% 3.68/0.99  git: last_make_outside_of_git: false
% 3.68/0.99  
% 3.68/0.99  ------ 
% 3.68/0.99  ------ Parsing...
% 3.68/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  ------ Proving...
% 3.68/0.99  ------ Problem Properties 
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  clauses                                 23
% 3.68/0.99  conjectures                             4
% 3.68/0.99  EPR                                     7
% 3.68/0.99  Horn                                    18
% 3.68/0.99  unary                                   4
% 3.68/0.99  binary                                  5
% 3.68/0.99  lits                                    67
% 3.68/0.99  lits eq                                 3
% 3.68/0.99  fd_pure                                 0
% 3.68/0.99  fd_pseudo                               0
% 3.68/0.99  fd_cond                                 0
% 3.68/0.99  fd_pseudo_cond                          0
% 3.68/0.99  AC symbols                              0
% 3.68/0.99  
% 3.68/0.99  ------ Input Options Time Limit: Unbounded
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing...
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.68/0.99  Current options:
% 3.68/0.99  ------ 
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing...
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  % SZS output start Saturation for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  fof(f1,axiom,(
% 3.68/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f9,plain,(
% 3.68/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f1])).
% 3.68/0.99  
% 3.68/0.99  fof(f16,plain,(
% 3.68/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.68/0.99    inference(nnf_transformation,[],[f9])).
% 3.68/0.99  
% 3.68/0.99  fof(f17,plain,(
% 3.68/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.68/0.99    inference(rectify,[],[f16])).
% 3.68/0.99  
% 3.68/0.99  fof(f18,plain,(
% 3.68/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f19,plain,(
% 3.68/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 3.68/0.99  
% 3.68/0.99  fof(f34,plain,(
% 3.68/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f19])).
% 3.68/0.99  
% 3.68/0.99  fof(f35,plain,(
% 3.68/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f19])).
% 3.68/0.99  
% 3.68/0.99  fof(f13,plain,(
% 3.68/0.99    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 3.68/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.68/0.99  
% 3.68/0.99  fof(f22,plain,(
% 3.68/0.99    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.68/0.99    inference(nnf_transformation,[],[f13])).
% 3.68/0.99  
% 3.68/0.99  fof(f23,plain,(
% 3.68/0.99    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.68/0.99    inference(flattening,[],[f22])).
% 3.68/0.99  
% 3.68/0.99  fof(f24,plain,(
% 3.68/0.99    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.68/0.99    inference(rectify,[],[f23])).
% 3.68/0.99  
% 3.68/0.99  fof(f27,plain,(
% 3.68/0.99    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f26,plain,(
% 3.68/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f25,plain,(
% 3.68/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK3(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f28,plain,(
% 3.68/0.99    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 3.68/0.99  
% 3.68/0.99  fof(f46,plain,(
% 3.68/0.99    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f2,axiom,(
% 3.68/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f20,plain,(
% 3.68/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.68/0.99    inference(nnf_transformation,[],[f2])).
% 3.68/0.99  
% 3.68/0.99  fof(f36,plain,(
% 3.68/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f20])).
% 3.68/0.99  
% 3.68/0.99  fof(f33,plain,(
% 3.68/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f19])).
% 3.68/0.99  
% 3.68/0.99  fof(f45,plain,(
% 3.68/0.99    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f6,conjecture,(
% 3.68/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f7,negated_conjecture,(
% 3.68/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.68/0.99    inference(negated_conjecture,[],[f6])).
% 3.68/0.99  
% 3.68/0.99  fof(f12,plain,(
% 3.68/0.99    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.68/0.99    inference(ennf_transformation,[],[f7])).
% 3.68/0.99  
% 3.68/0.99  fof(f31,plain,(
% 3.68/0.99    ( ! [X0,X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f30,plain,(
% 3.68/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) => (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))) & m1_pre_topc(sK7,X0))) )),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f29,plain,(
% 3.68/0.99    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,sK6)) & l1_pre_topc(sK6))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f32,plain,(
% 3.68/0.99    ((~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))) & m1_pre_topc(sK7,sK6)) & l1_pre_topc(sK6)),
% 3.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f12,f31,f30,f29])).
% 3.68/0.99  
% 3.68/0.99  fof(f54,plain,(
% 3.68/0.99    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))),
% 3.68/0.99    inference(cnf_transformation,[],[f32])).
% 3.68/0.99  
% 3.68/0.99  fof(f41,plain,(
% 3.68/0.99    ( ! [X0,X5,X1] : (m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f37,plain,(
% 3.68/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f20])).
% 3.68/0.99  
% 3.68/0.99  fof(f44,plain,(
% 3.68/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,u1_pre_topc(X0)) | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f56,plain,(
% 3.68/0.99    ( ! [X6,X0,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0)) | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 3.68/0.99    inference(equality_resolution,[],[f44])).
% 3.68/0.99  
% 3.68/0.99  fof(f47,plain,(
% 3.68/0.99    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) | r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f48,plain,(
% 3.68/0.99    ( ! [X0,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = sK3(X0,X1) | r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f42,plain,(
% 3.68/0.99    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f43,plain,(
% 3.68/0.99    ( ! [X0,X5,X1] : (k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5 | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f49,plain,(
% 3.68/0.99    ( ! [X0,X3,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f53,plain,(
% 3.68/0.99    m1_pre_topc(sK7,sK6)),
% 3.68/0.99    inference(cnf_transformation,[],[f32])).
% 3.68/0.99  
% 3.68/0.99  fof(f52,plain,(
% 3.68/0.99    l1_pre_topc(sK6)),
% 3.68/0.99    inference(cnf_transformation,[],[f32])).
% 3.68/0.99  
% 3.68/0.99  fof(f3,axiom,(
% 3.68/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f10,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.68/0.99    inference(ennf_transformation,[],[f3])).
% 3.68/0.99  
% 3.68/0.99  fof(f14,plain,(
% 3.68/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 3.68/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.68/0.99  
% 3.68/0.99  fof(f15,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.68/0.99    inference(definition_folding,[],[f10,f14,f13])).
% 3.68/0.99  
% 3.68/0.99  fof(f50,plain,(
% 3.68/0.99    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f15])).
% 3.68/0.99  
% 3.68/0.99  fof(f21,plain,(
% 3.68/0.99    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 3.68/0.99    inference(nnf_transformation,[],[f14])).
% 3.68/0.99  
% 3.68/0.99  fof(f38,plain,(
% 3.68/0.99    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f21])).
% 3.68/0.99  
% 3.68/0.99  fof(f55,plain,(
% 3.68/0.99    ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.68/0.99    inference(cnf_transformation,[],[f32])).
% 3.68/0.99  
% 3.68/0.99  fof(f39,plain,(
% 3.68/0.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f21])).
% 3.68/0.99  
% 3.68/0.99  cnf(c_249,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1,plain,
% 3.68/0.99      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1851,plain,
% 3.68/0.99      ( r2_hidden(sK2(X0,X1),X0) = iProver_top
% 3.68/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_0,plain,
% 3.68/0.99      ( ~ r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1852,plain,
% 3.68/0.99      ( r2_hidden(sK2(X0,X1),X1) != iProver_top
% 3.68/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2534,plain,
% 3.68/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1851,c_1852]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_10,plain,
% 3.68/0.99      ( sP0(X0,X1)
% 3.68/0.99      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.99      | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
% 3.68/0.99      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1321,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.68/0.99      | ~ iProver_ARSWP_67
% 3.68/0.99      | arAF0_sP0_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1837,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_67 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2450,plain,
% 3.68/0.99      ( r1_tarski(X0,X0) ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3271,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ iProver_ARSWP_67
% 3.68/0.99      | arAF0_sP0_0 ),
% 3.68/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2450,c_1321]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3280,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_67 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_3271]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5083,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.68/0.99      | iProver_ARSWP_67 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1837,c_3280]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5084,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_67 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_5083]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1848,plain,
% 3.68/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.68/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5091,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(arAF0_sK4_0,u1_struct_0(X0)) = iProver_top
% 3.68/0.99      | iProver_ARSWP_67 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_5084,c_1848]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.68/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1850,plain,
% 3.68/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.68/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.68/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2626,plain,
% 3.68/0.99      ( r2_hidden(sK2(X0,X1),X2) = iProver_top
% 3.68/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.68/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1851,c_1850]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3220,plain,
% 3.68/0.99      ( r2_hidden(sK2(X0,X1),X2) = iProver_top
% 3.68/0.99      | r1_tarski(X0,X3) != iProver_top
% 3.68/0.99      | r1_tarski(X3,X2) != iProver_top
% 3.68/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2626,c_1850]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5114,plain,
% 3.68/0.99      ( r2_hidden(sK2(arAF0_sK4_0,X0),X1) = iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(u1_struct_0(X2),X1) != iProver_top
% 3.68/0.99      | r1_tarski(arAF0_sK4_0,X0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_67 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_5091,c_3220]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5791,plain,
% 3.68/0.99      ( r2_hidden(sK2(arAF0_sK4_0,X0),u1_struct_0(X1)) = iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(arAF0_sK4_0,X0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_67 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2534,c_5114]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_11,plain,
% 3.68/0.99      ( sP0(X0,X1)
% 3.68/0.99      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.99      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1322,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.99      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.68/0.99      | ~ iProver_ARSWP_68
% 3.68/0.99      | arAF0_sP0_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1836,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.68/0.99      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_68 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3272,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.99      | ~ iProver_ARSWP_68
% 3.68/0.99      | arAF0_sP0_0 ),
% 3.68/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2450,c_1322]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3277,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.68/0.99      | iProver_ARSWP_68 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_3272]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3385,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.68/0.99      | iProver_ARSWP_68 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1836,c_3277]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3392,plain,
% 3.68/0.99      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 3.68/0.99      | iProver_ARSWP_68 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3385,c_1848]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4927,plain,
% 3.68/0.99      ( r2_hidden(sK2(arAF0_sK3_0,X0),X1) = iProver_top
% 3.68/0.99      | r1_tarski(u1_struct_0(X2),X1) != iProver_top
% 3.68/0.99      | r1_tarski(arAF0_sK3_0,X0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_68 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3392,c_3220]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5634,plain,
% 3.68/0.99      ( r2_hidden(sK2(arAF0_sK3_0,X0),u1_struct_0(X1)) = iProver_top
% 3.68/0.99      | r1_tarski(arAF0_sK3_0,X0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_68 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2534,c_4927]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_20,negated_conjecture,
% 3.68/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1846,plain,
% 3.68/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_15,plain,
% 3.68/0.99      ( ~ sP0(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.99      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.99      | ~ r2_hidden(X2,u1_pre_topc(X0)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1326,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.99      | m1_subset_1(arAF0_sK5_0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.68/0.99      | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ iProver_ARSWP_72
% 3.68/0.99      | ~ arAF0_sP0_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_15]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1832,plain,
% 3.68/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.68/0.99      | m1_subset_1(arAF0_sK5_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 3.68/0.99      | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_72 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2410,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK5_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.68/0.99      | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_72 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1846,c_1832]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2714,plain,
% 3.68/0.99      ( r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r1_tarski(arAF0_sK5_0,u1_struct_0(X0)) = iProver_top
% 3.68/0.99      | iProver_ARSWP_72 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2410,c_1848]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4928,plain,
% 3.68/0.99      ( r2_hidden(sK2(arAF0_sK5_0,X0),X1) = iProver_top
% 3.68/0.99      | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r1_tarski(u1_struct_0(X2),X1) != iProver_top
% 3.68/0.99      | r1_tarski(arAF0_sK5_0,X0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_72 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2714,c_3220]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5519,plain,
% 3.68/0.99      ( r2_hidden(sK2(arAF0_sK5_0,X0),u1_struct_0(X1)) = iProver_top
% 3.68/0.99      | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r1_tarski(arAF0_sK5_0,X0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_72 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2534,c_4928]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2295,plain,
% 3.68/0.99      ( r1_tarski(sK8,u1_struct_0(sK7)) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1846,c_1848]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4925,plain,
% 3.68/0.99      ( r2_hidden(sK2(sK8,X0),X1) = iProver_top
% 3.68/0.99      | r1_tarski(u1_struct_0(sK7),X1) != iProver_top
% 3.68/0.99      | r1_tarski(sK8,X0) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2295,c_3220]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5248,plain,
% 3.68/0.99      ( r2_hidden(sK2(sK8,X0),X1) = iProver_top
% 3.68/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.68/0.99      | r1_tarski(u1_struct_0(sK7),X2) != iProver_top
% 3.68/0.99      | r1_tarski(sK8,X0) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_4925,c_1850]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5247,plain,
% 3.68/0.99      ( r1_tarski(u1_struct_0(sK7),X0) != iProver_top
% 3.68/0.99      | r1_tarski(sK8,X0) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_4925,c_1852]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3,plain,
% 3.68/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1849,plain,
% 3.68/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.68/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_12,plain,
% 3.68/0.99      ( ~ sP0(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.99      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.99      | ~ r2_hidden(X2,u1_pre_topc(X1))
% 3.68/0.99      | r2_hidden(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),u1_pre_topc(X0)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1323,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.99      | ~ m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.68/0.99      | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ iProver_ARSWP_69
% 3.68/0.99      | ~ arAF0_sP0_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1835,plain,
% 3.68/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.68/0.99      | m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.68/0.99      | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_69 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4025,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.68/0.99      | r2_hidden(X1,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
% 3.68/0.99      | iProver_ARSWP_69 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1849,c_1835]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4675,plain,
% 3.68/0.99      ( r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 3.68/0.99      | r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X2)) != iProver_top
% 3.68/0.99      | iProver_ARSWP_69 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1849,c_4025]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4787,plain,
% 3.68/0.99      ( r2_hidden(u1_struct_0(X0),arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X1)) != iProver_top
% 3.68/0.99      | iProver_ARSWP_69 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2534,c_4675]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4026,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_69 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1846,c_1835]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4499,plain,
% 3.68/0.99      ( r2_hidden(arAF0_k9_subset_1_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) != iProver_top
% 3.68/0.99      | iProver_ARSWP_69 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1849,c_4026]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_9,plain,
% 3.68/0.99      ( sP0(X0,X1)
% 3.68/0.99      | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
% 3.68/0.99      | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
% 3.68/0.99      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1320,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.68/0.99      | ~ iProver_ARSWP_66
% 3.68/0.99      | arAF0_sP0_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1838,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_66 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1320]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3273,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ iProver_ARSWP_66
% 3.68/0.99      | arAF0_sP0_0 ),
% 3.68/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2450,c_1320]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3276,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_66 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_3273]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4381,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_66 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1838,c_3276]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4382,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK4_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_66 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_4381]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4389,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK4_0,X0) = iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(arAF0_u1_pre_topc_0,X0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_66 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_4382,c_1850]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8,plain,
% 3.68/0.99      ( sP0(X0,X1)
% 3.68/0.99      | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
% 3.68/0.99      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
% 3.68/0.99      | k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = sK3(X0,X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1319,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.68/0.99      | ~ iProver_ARSWP_65
% 3.68/0.99      | arAF0_sP0_0
% 3.68/0.99      | arAF0_k9_subset_1_0 = arAF0_sK3_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1839,plain,
% 3.68/0.99      ( arAF0_k9_subset_1_0 = arAF0_sK3_0
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_65 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3274,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ iProver_ARSWP_65
% 3.68/0.99      | arAF0_sP0_0
% 3.68/0.99      | arAF0_k9_subset_1_0 = arAF0_sK3_0 ),
% 3.68/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2450,c_1319]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3275,plain,
% 3.68/0.99      ( arAF0_k9_subset_1_0 = arAF0_sK3_0
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_65 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_3274]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4200,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | arAF0_k9_subset_1_0 = arAF0_sK3_0
% 3.68/0.99      | iProver_ARSWP_65 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1839,c_3275]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4201,plain,
% 3.68/0.99      ( arAF0_k9_subset_1_0 = arAF0_sK3_0
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_65 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_4200]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4208,plain,
% 3.68/0.99      ( arAF0_k9_subset_1_0 = arAF0_sK3_0
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,X0) = iProver_top
% 3.68/0.99      | r1_tarski(arAF0_u1_pre_topc_0,X0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_65 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_4201,c_1850]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2419,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK5_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.68/0.99      | r2_hidden(X1,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
% 3.68/0.99      | iProver_ARSWP_72 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1849,c_1832]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4005,plain,
% 3.68/0.99      ( m1_subset_1(arAF0_sK5_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.68/0.99      | r2_hidden(u1_struct_0(X1),arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_72 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2534,c_2419]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_14,plain,
% 3.68/0.99      ( ~ sP0(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.99      | ~ r2_hidden(X2,u1_pre_topc(X0))
% 3.68/0.99      | r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X1)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1325,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.99      | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ iProver_ARSWP_71
% 3.68/0.99      | ~ arAF0_sP0_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_14]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1833,plain,
% 3.68/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.68/0.99      | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_71 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1325]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3077,plain,
% 3.68/0.99      ( r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 3.68/0.99      | iProver_ARSWP_71 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1849,c_1833]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3841,plain,
% 3.68/0.99      ( r2_hidden(u1_struct_0(X0),arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | iProver_ARSWP_71 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2534,c_3077]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_13,plain,
% 3.68/0.99      ( ~ sP0(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.68/0.99      | ~ r2_hidden(X2,u1_pre_topc(X0))
% 3.68/0.99      | k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2),k2_struct_0(X0)) = X2 ),
% 3.68/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1324,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.99      | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ iProver_ARSWP_70
% 3.68/0.99      | ~ arAF0_sP0_0
% 3.68/0.99      | arAF0_k9_subset_1_0 = X0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_13]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1834,plain,
% 3.68/0.99      ( arAF0_k9_subset_1_0 = X0
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.68/0.99      | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_70 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3410,plain,
% 3.68/0.99      ( arAF0_k9_subset_1_0 = X0
% 3.68/0.99      | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 3.68/0.99      | iProver_ARSWP_70 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1849,c_1834]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3669,plain,
% 3.68/0.99      ( u1_struct_0(X0) = arAF0_k9_subset_1_0
% 3.68/0.99      | r2_hidden(u1_struct_0(X0),arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_70 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2534,c_3410]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3413,plain,
% 3.68/0.99      ( arAF0_sK5_0 = arAF0_k9_subset_1_0
% 3.68/0.99      | r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_72 != iProver_top
% 3.68/0.99      | iProver_ARSWP_70 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2410,c_1834]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3411,plain,
% 3.68/0.99      ( arAF0_k9_subset_1_0 = sK8
% 3.68/0.99      | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_70 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1846,c_1834]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7,plain,
% 3.68/0.99      ( sP0(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.99      | ~ r2_hidden(X2,u1_pre_topc(X1))
% 3.68/0.99      | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X0))
% 3.68/0.99      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
% 3.68/0.99      | k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)) != sK3(X0,X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1318,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.99      | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.68/0.99      | ~ iProver_ARSWP_64
% 3.68/0.99      | arAF0_sP0_0
% 3.68/0.99      | arAF0_k9_subset_1_0 != arAF0_sK3_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1840,plain,
% 3.68/0.99      ( arAF0_k9_subset_1_0 != arAF0_sK3_0
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.68/0.99      | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_64 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3270,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.68/0.99      | ~ r2_hidden(X0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0)
% 3.68/0.99      | ~ iProver_ARSWP_64
% 3.68/0.99      | arAF0_sP0_0
% 3.68/0.99      | arAF0_k9_subset_1_0 != arAF0_sK3_0 ),
% 3.68/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2450,c_1318]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3283,plain,
% 3.68/0.99      ( arAF0_k9_subset_1_0 != arAF0_sK3_0
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.68/0.99      | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_64 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_3270]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4910,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.68/0.99      | arAF0_k9_subset_1_0 != arAF0_sK3_0
% 3.68/0.99      | iProver_ARSWP_64 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1840,c_3283]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4911,plain,
% 3.68/0.99      ( arAF0_k9_subset_1_0 != arAF0_sK3_0
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.68/0.99      | r2_hidden(X0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | r2_hidden(arAF0_sK3_0,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_64 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_4910]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3078,plain,
% 3.68/0.99      ( r2_hidden(arAF0_sK5_0,arAF0_u1_pre_topc_0) = iProver_top
% 3.68/0.99      | r2_hidden(sK8,arAF0_u1_pre_topc_0) != iProver_top
% 3.68/0.99      | iProver_ARSWP_71 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1846,c_1833]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_21,negated_conjecture,
% 3.68/0.99      ( m1_pre_topc(sK7,sK6) ),
% 3.68/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1330,negated_conjecture,
% 3.68/0.99      ( ~ iProver_ARSWP_76 | arAF0_m1_pre_topc_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_21]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1829,plain,
% 3.68/0.99      ( iProver_ARSWP_76 != iProver_top | arAF0_m1_pre_topc_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_22,negated_conjecture,
% 3.68/0.99      ( l1_pre_topc(sK6) ),
% 3.68/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1331,negated_conjecture,
% 3.68/0.99      ( ~ iProver_ARSWP_77 | arAF0_l1_pre_topc_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_22]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1828,plain,
% 3.68/0.99      ( iProver_ARSWP_77 != iProver_top | arAF0_l1_pre_topc_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1331]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_17,plain,
% 3.68/0.99      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1328,plain,
% 3.68/0.99      ( ~ iProver_ARSWP_74 | ~ arAF0_l1_pre_topc_0 | arAF0_sP1_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_17]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1830,plain,
% 3.68/0.99      ( iProver_ARSWP_74 != iProver_top
% 3.68/0.99      | arAF0_l1_pre_topc_0 != iProver_top
% 3.68/0.99      | arAF0_sP1_0 = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2219,plain,
% 3.68/0.99      ( iProver_ARSWP_77 != iProver_top
% 3.68/0.99      | iProver_ARSWP_74 != iProver_top
% 3.68/0.99      | arAF0_sP1_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1828,c_1830]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6,plain,
% 3.68/0.99      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1317,plain,
% 3.68/0.99      ( ~ iProver_ARSWP_63
% 3.68/0.99      | ~ arAF0_m1_pre_topc_0
% 3.68/0.99      | arAF0_sP0_0
% 3.68/0.99      | ~ arAF0_sP1_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1841,plain,
% 3.68/0.99      ( iProver_ARSWP_63 != iProver_top
% 3.68/0.99      | arAF0_m1_pre_topc_0 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top
% 3.68/0.99      | arAF0_sP1_0 != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1317]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2829,plain,
% 3.68/0.99      ( iProver_ARSWP_77 != iProver_top
% 3.68/0.99      | iProver_ARSWP_74 != iProver_top
% 3.68/0.99      | iProver_ARSWP_63 != iProver_top
% 3.68/0.99      | arAF0_m1_pre_topc_0 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2219,c_1841]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2953,plain,
% 3.68/0.99      ( iProver_ARSWP_77 != iProver_top
% 3.68/0.99      | iProver_ARSWP_76 != iProver_top
% 3.68/0.99      | iProver_ARSWP_74 != iProver_top
% 3.68/0.99      | iProver_ARSWP_63 != iProver_top
% 3.68/0.99      | arAF0_sP0_0 = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1829,c_2829]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_19,negated_conjecture,
% 3.68/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1847,plain,
% 3.68/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2418,plain,
% 3.68/0.99      ( r1_tarski(sK8,u1_struct_0(sK6)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1849,c_1847]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5,plain,
% 3.68/0.99      ( ~ sP1(X0,X1) | ~ sP0(X1,X0) | m1_pre_topc(X1,X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1316,plain,
% 3.68/0.99      ( ~ iProver_ARSWP_62
% 3.68/0.99      | arAF0_m1_pre_topc_0
% 3.68/0.99      | ~ arAF0_sP0_0
% 3.68/0.99      | ~ arAF0_sP1_0 ),
% 3.68/0.99      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1842,plain,
% 3.68/0.99      ( iProver_ARSWP_62 != iProver_top
% 3.68/0.99      | arAF0_m1_pre_topc_0 = iProver_top
% 3.68/0.99      | arAF0_sP0_0 != iProver_top
% 3.68/0.99      | arAF0_sP1_0 != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1316]) ).
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  % SZS output end Saturation for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  ------                               Statistics
% 3.68/0.99  
% 3.68/0.99  ------ Selected
% 3.68/0.99  
% 3.68/0.99  total_time:                             0.197
% 3.68/0.99  
%------------------------------------------------------------------------------
