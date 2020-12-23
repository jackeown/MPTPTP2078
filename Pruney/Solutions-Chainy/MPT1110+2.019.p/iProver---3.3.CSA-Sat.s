%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:28 EST 2020

% Result     : CounterSatisfiable 3.97s
% Output     : Saturation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  190 (3454 expanded)
%              Number of clauses        :  142 (1228 expanded)
%              Number of leaves         :   15 (1039 expanded)
%              Depth                    :   16
%              Number of atoms          : 1014 (17529 expanded)
%              Number of equality atoms :  670 (3566 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
        & m1_pre_topc(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,sK5) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_pre_topc(sK6,sK5)
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f14,f29,f28,f27])).

fof(f49,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
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
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f16,f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f15])).

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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1)
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_241,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3041,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2526,plain,
    ( arAF0_sP1_0_1(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ iProver_ARSWP_103 ),
    inference(arg_filter_abstr,[status(unp)],[c_16])).

cnf(c_3025,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_103 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2526])).

cnf(c_3393,plain,
    ( arAF0_sP1_0_1(X0)
    | ~ l1_pre_topc(X0)
    | ~ iProver_ARSWP_103 ),
    inference(resolution,[status(thm)],[c_2526,c_21])).

cnf(c_3394,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_103 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3393])).

cnf(c_3826,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_103 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3025,c_3394])).

cnf(c_3833,plain,
    ( arAF0_sP1_0_1(sK5) = iProver_top
    | iProver_ARSWP_103 != iProver_top ),
    inference(superposition,[status(thm)],[c_3041,c_3826])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2528,negated_conjecture,
    ( arAF0_m1_pre_topc_0_1(sK6)
    | ~ iProver_ARSWP_105 ),
    inference(arg_filter_abstr,[status(unp)],[c_20])).

cnf(c_3023,plain,
    ( arAF0_m1_pre_topc_0_1(sK6) = iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2528])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2515,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | arAF0_sP0_0_1(X0)
    | ~ arAF0_sP1_0_1(X1)
    | ~ iProver_ARSWP_92 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_3034,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | arAF0_sP1_0_1(X1) != iProver_top
    | iProver_ARSWP_92 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2515])).

cnf(c_4089,plain,
    ( arAF0_sP0_0_1(sK6) = iProver_top
    | arAF0_sP1_0_1(X0) != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_92 != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_3034])).

cnf(c_4381,plain,
    ( arAF0_sP0_0_1(sK6) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_92 != iProver_top ),
    inference(superposition,[status(thm)],[c_3833,c_4089])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2525,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_102 ),
    inference(arg_filter_abstr,[status(unp)],[c_15])).

cnf(c_3026,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | iProver_ARSWP_102 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2525])).

cnf(c_4543,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_92 != iProver_top ),
    inference(superposition,[status(thm)],[c_4381,c_3026])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3042,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3044,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3367,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_3044])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2513,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ iProver_ARSWP_90
    | arAF0_k2_xboole_0_0 = X1 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_3036,plain,
    ( arAF0_k2_xboole_0_0 = X0
    | r1_tarski(X1,X0) != iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2513])).

cnf(c_3508,plain,
    ( u1_struct_0(sK6) = arAF0_k2_xboole_0_0
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_3036])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2519,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_96
    | arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_3030,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_96 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2519])).

cnf(c_6106,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_96 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_3044])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2514,plain,
    ( arAF0_m1_pre_topc_0_1(X0)
    | ~ arAF0_sP0_0_1(X0)
    | ~ arAF0_sP1_0_1(X1)
    | ~ iProver_ARSWP_91 ),
    inference(arg_filter_abstr,[status(unp)],[c_4])).

cnf(c_3035,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | arAF0_sP1_0_1(X1) != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2514])).

cnf(c_4202,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3833,c_3035])).

cnf(c_6289,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6106,c_4202])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2527,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_104 ),
    inference(arg_filter_abstr,[status(unp)],[c_17])).

cnf(c_3024,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2527])).

cnf(c_3453,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_104 ),
    inference(resolution,[status(thm)],[c_2527,c_21])).

cnf(c_3454,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3453])).

cnf(c_3495,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3024,c_3454])).

cnf(c_6932,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6289,c_3495])).

cnf(c_9135,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6932,c_3826])).

cnf(c_10538,plain,
    ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_9135])).

cnf(c_11079,plain,
    ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_10538])).

cnf(c_10542,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_9135,c_3036])).

cnf(c_10851,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_10542])).

cnf(c_10,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2520,plain,
    ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_97 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_3029,plain,
    ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2520])).

cnf(c_5180,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_sK2_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_3029,c_3044])).

cnf(c_5341,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_5180,c_3036])).

cnf(c_7851,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_5341])).

cnf(c_8632,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_7851,c_4202])).

cnf(c_8949,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_8632,c_3495])).

cnf(c_10525,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_8949,c_3826])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2517,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_94
    | arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 = arAF0_sK2_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_3032,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_94 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2517])).

cnf(c_5372,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_94 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_3032])).

cnf(c_8143,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_94 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5372,c_4202])).

cnf(c_8328,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_94 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8143,c_3495])).

cnf(c_10279,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_94 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8328,c_3826])).

cnf(c_6099,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_3030])).

cnf(c_6744,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6099,c_4202])).

cnf(c_7198,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6744,c_3495])).

cnf(c_10244,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7198,c_3826])).

cnf(c_8,plain,
    ( r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2518,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_95
    | arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_3031,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_95 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2518])).

cnf(c_4857,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_95 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_3031])).

cnf(c_8102,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_95 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4857,c_4202])).

cnf(c_8288,plain,
    ( l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_95 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8102,c_3495])).

cnf(c_10013,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_95 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8288,c_3826])).

cnf(c_4858,plain,
    ( arAF0_k2_struct_0_0 = arAF0_k2_xboole_0_0
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_3036])).

cnf(c_7550,plain,
    ( r1_tarski(arAF0_k2_xboole_0_0,arAF0_k2_xboole_0_0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_4858,c_4543])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2512,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(arAF0_k2_xboole_0_0,X1)
    | ~ iProver_ARSWP_89 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_3037,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(arAF0_k2_xboole_0_0,X1) != iProver_top
    | iProver_ARSWP_89 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2512])).

cnf(c_8583,plain,
    ( r1_tarski(X0,arAF0_k2_xboole_0_0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | iProver_ARSWP_89 != iProver_top ),
    inference(superposition,[status(thm)],[c_7550,c_3037])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3045,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2522,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_99
    | ~ arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_3028,plain,
    ( arAF0_k9_subset_1_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2522])).

cnf(c_5006,plain,
    ( arAF0_k9_subset_1_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) != iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_3028])).

cnf(c_5737,plain,
    ( arAF0_k9_subset_1_0 = X0
    | r1_tarski(X0,arAF0_k2_xboole_0_0) != iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3045,c_5006])).

cnf(c_9480,plain,
    ( arAF0_k9_subset_1_0 = X0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | iProver_ARSWP_89 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8583,c_5737])).

cnf(c_9771,plain,
    ( arAF0_k9_subset_1_0 = X0
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | iProver_ARSWP_89 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9480,c_4381])).

cnf(c_9137,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6932,c_3036])).

cnf(c_9641,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_9137])).

cnf(c_8585,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k2_xboole_0_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_7550,c_5737])).

cnf(c_9619,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k2_xboole_0_0
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8585,c_4381])).

cnf(c_6101,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_4202])).

cnf(c_7010,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6101,c_3495])).

cnf(c_9447,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7010,c_3826])).

cnf(c_9134,plain,
    ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_6932])).

cnf(c_9206,plain,
    ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_9134])).

cnf(c_6934,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6289,c_3036])).

cnf(c_8990,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_6934])).

cnf(c_6295,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6106,c_3036])).

cnf(c_7898,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_6295])).

cnf(c_6930,plain,
    ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_6289])).

cnf(c_7184,plain,
    ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_6930])).

cnf(c_6287,plain,
    ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_6106])).

cnf(c_6732,plain,
    ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_6287])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_101
    | ~ arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_14])).

cnf(c_3027,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2524])).

cnf(c_4046,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_3027])).

cnf(c_4232,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_4046])).

cnf(c_5739,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4232,c_5006])).

cnf(c_5780,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4381,c_5739])).

cnf(c_5005,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(X0) != iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4046,c_3028])).

cnf(c_5510,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4381,c_5005])).

cnf(c_5930,plain,
    ( iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | arAF0_sK4_0 = arAF0_k9_subset_1_0
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5780,c_4381,c_5510])).

cnf(c_5931,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(renaming,[status(thm)],[c_5930])).

cnf(c_5340,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_sK2_0,arAF0_k2_xboole_0_0) = iProver_top
    | arAF0_sP0_0_1(sK6) = iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_5180])).

cnf(c_5179,plain,
    ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(sK6) = iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_3029])).

cnf(c_5004,plain,
    ( arAF0_k9_subset_1_0 = sK7
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_3028])).

cnf(c_5172,plain,
    ( arAF0_k9_subset_1_0 = sK7
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4381,c_5004])).

cnf(c_5003,plain,
    ( arAF0_k9_subset_1_0 = X0
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3045,c_3028])).

cnf(c_4233,plain,
    ( r1_tarski(arAF0_sK4_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4046,c_3044])).

cnf(c_4351,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4233,c_3036])).

cnf(c_4693,plain,
    ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4381,c_4351])).

cnf(c_4350,plain,
    ( r1_tarski(arAF0_sK4_0,arAF0_k2_xboole_0_0) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_90 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_4233])).

cnf(c_4045,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
    | arAF0_sP0_0_1(X2) != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3045,c_3027])).

cnf(c_3502,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_3495])).

cnf(c_3834,plain,
    ( arAF0_sP1_0_1(sK6) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top ),
    inference(superposition,[status(thm)],[c_3502,c_3826])).

cnf(c_3728,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_3042])).

cnf(c_3727,plain,
    ( r1_tarski(sK7,arAF0_k2_xboole_0_0) = iProver_top
    | iProver_ARSWP_90 != iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_3367])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3043,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3429,plain,
    ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3045,c_3043])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(sK2(X2,X1),u1_pre_topc(X2))
    | sP0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)) != sK2(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X2)
    | ~ iProver_ARSWP_93
    | ~ arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 != arAF0_sK2_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_3033,plain,
    ( arAF0_k9_subset_1_0 != arAF0_sK2_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X2) = iProver_top
    | iProver_ARSWP_93 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2516])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.97/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.01  
% 3.97/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/1.01  
% 3.97/1.01  ------  iProver source info
% 3.97/1.01  
% 3.97/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.97/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/1.01  git: non_committed_changes: false
% 3.97/1.01  git: last_make_outside_of_git: false
% 3.97/1.01  
% 3.97/1.01  ------ 
% 3.97/1.01  ------ Parsing...
% 3.97/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/1.01  ------ Proving...
% 3.97/1.01  ------ Problem Properties 
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  clauses                                 22
% 3.97/1.01  conjectures                             4
% 3.97/1.01  EPR                                     6
% 3.97/1.01  Horn                                    18
% 3.97/1.01  unary                                   4
% 3.97/1.01  binary                                  5
% 3.97/1.01  lits                                    64
% 3.97/1.01  lits eq                                 4
% 3.97/1.01  fd_pure                                 0
% 3.97/1.01  fd_pseudo                               0
% 3.97/1.01  fd_cond                                 0
% 3.97/1.01  fd_pseudo_cond                          0
% 3.97/1.01  AC symbols                              0
% 3.97/1.01  
% 3.97/1.01  ------ Input Options Time Limit: Unbounded
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing...
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.97/1.01  Current options:
% 3.97/1.01  ------ 
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Proving...
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing...
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing...
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing...
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/1.01  
% 3.97/1.01  ------ Proving...
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/1.01  
% 3.97/1.01  ------ Proving...
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.97/1.01  
% 3.97/1.01  ------ Proving...
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.97/1.01  
% 3.97/1.01  ------ Proving...
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/1.01  
% 3.97/1.01  ------ Proving...
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.97/1.01  
% 3.97/1.01  ------ Proving...
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.97/1.01  
% 3.97/1.01  ------ Proving...
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/1.01  
% 3.97/1.01  ------ Proving...
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 3.97/1.01  
% 3.97/1.01  % SZS output start Saturation for theBenchmark.p
% 3.97/1.01  
% 3.97/1.01  fof(f7,conjecture,(
% 3.97/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f8,negated_conjecture,(
% 3.97/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.97/1.01    inference(negated_conjecture,[],[f7])).
% 3.97/1.01  
% 3.97/1.01  fof(f14,plain,(
% 3.97/1.01    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.97/1.01    inference(ennf_transformation,[],[f8])).
% 3.97/1.01  
% 3.97/1.01  fof(f29,plain,(
% 3.97/1.01    ( ! [X0,X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f28,plain,(
% 3.97/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) => (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_pre_topc(sK6,X0))) )),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f27,plain,(
% 3.97/1.01    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,sK5)) & l1_pre_topc(sK5))),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f30,plain,(
% 3.97/1.01    ((~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_pre_topc(sK6,sK5)) & l1_pre_topc(sK5)),
% 3.97/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f14,f29,f28,f27])).
% 3.97/1.01  
% 3.97/1.01  fof(f49,plain,(
% 3.97/1.01    l1_pre_topc(sK5)),
% 3.97/1.01    inference(cnf_transformation,[],[f30])).
% 3.97/1.01  
% 3.97/1.01  fof(f4,axiom,(
% 3.97/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f12,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(ennf_transformation,[],[f4])).
% 3.97/1.01  
% 3.97/1.01  fof(f16,plain,(
% 3.97/1.01    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 3.97/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.97/1.01  
% 3.97/1.01  fof(f15,plain,(
% 3.97/1.01    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 3.97/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.97/1.01  
% 3.97/1.01  fof(f17,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(definition_folding,[],[f12,f16,f15])).
% 3.97/1.01  
% 3.97/1.01  fof(f47,plain,(
% 3.97/1.01    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f17])).
% 3.97/1.01  
% 3.97/1.01  fof(f50,plain,(
% 3.97/1.01    m1_pre_topc(sK6,sK5)),
% 3.97/1.01    inference(cnf_transformation,[],[f30])).
% 3.97/1.01  
% 3.97/1.01  fof(f19,plain,(
% 3.97/1.01    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 3.97/1.01    inference(nnf_transformation,[],[f16])).
% 3.97/1.01  
% 3.97/1.01  fof(f35,plain,(
% 3.97/1.01    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f19])).
% 3.97/1.01  
% 3.97/1.01  fof(f20,plain,(
% 3.97/1.01    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.97/1.01    inference(nnf_transformation,[],[f15])).
% 3.97/1.01  
% 3.97/1.01  fof(f21,plain,(
% 3.97/1.01    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.97/1.01    inference(flattening,[],[f20])).
% 3.97/1.01  
% 3.97/1.01  fof(f22,plain,(
% 3.97/1.01    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.97/1.01    inference(rectify,[],[f21])).
% 3.97/1.01  
% 3.97/1.01  fof(f25,plain,(
% 3.97/1.01    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f24,plain,(
% 3.97/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f23,plain,(
% 3.97/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f26,plain,(
% 3.97/1.01    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.97/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).
% 3.97/1.01  
% 3.97/1.01  fof(f37,plain,(
% 3.97/1.01    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f26])).
% 3.97/1.01  
% 3.97/1.01  fof(f51,plain,(
% 3.97/1.01    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.97/1.01    inference(cnf_transformation,[],[f30])).
% 3.97/1.01  
% 3.97/1.01  fof(f3,axiom,(
% 3.97/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f18,plain,(
% 3.97/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.97/1.01    inference(nnf_transformation,[],[f3])).
% 3.97/1.01  
% 3.97/1.01  fof(f33,plain,(
% 3.97/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f18])).
% 3.97/1.01  
% 3.97/1.01  fof(f2,axiom,(
% 3.97/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f11,plain,(
% 3.97/1.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.97/1.01    inference(ennf_transformation,[],[f2])).
% 3.97/1.01  
% 3.97/1.01  fof(f32,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f11])).
% 3.97/1.01  
% 3.97/1.01  fof(f43,plain,(
% 3.97/1.01    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f26])).
% 3.97/1.01  
% 3.97/1.01  fof(f36,plain,(
% 3.97/1.01    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f19])).
% 3.97/1.01  
% 3.97/1.01  fof(f6,axiom,(
% 3.97/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f13,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(ennf_transformation,[],[f6])).
% 3.97/1.01  
% 3.97/1.01  fof(f48,plain,(
% 3.97/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f13])).
% 3.97/1.01  
% 3.97/1.01  fof(f42,plain,(
% 3.97/1.01    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f26])).
% 3.97/1.01  
% 3.97/1.01  fof(f45,plain,(
% 3.97/1.01    ( ! [X0,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f26])).
% 3.97/1.01  
% 3.97/1.01  fof(f44,plain,(
% 3.97/1.01    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f26])).
% 3.97/1.01  
% 3.97/1.01  fof(f1,axiom,(
% 3.97/1.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f10,plain,(
% 3.97/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.97/1.01    inference(ennf_transformation,[],[f1])).
% 3.97/1.01  
% 3.97/1.01  fof(f31,plain,(
% 3.97/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f10])).
% 3.97/1.01  
% 3.97/1.01  fof(f34,plain,(
% 3.97/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f18])).
% 3.97/1.01  
% 3.97/1.01  fof(f40,plain,(
% 3.97/1.01    ( ! [X0,X5,X1] : (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f26])).
% 3.97/1.01  
% 3.97/1.01  fof(f38,plain,(
% 3.97/1.01    ( ! [X0,X5,X1] : (m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f26])).
% 3.97/1.01  
% 3.97/1.01  fof(f52,plain,(
% 3.97/1.01    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))),
% 3.97/1.01    inference(cnf_transformation,[],[f30])).
% 3.97/1.01  
% 3.97/1.01  fof(f46,plain,(
% 3.97/1.01    ( ! [X0,X3,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f26])).
% 3.97/1.01  
% 3.97/1.01  cnf(c_241,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_21,negated_conjecture,
% 3.97/1.01      ( l1_pre_topc(sK5) ),
% 3.97/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3041,plain,
% 3.97/1.01      ( l1_pre_topc(sK5) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_16,plain,
% 3.97/1.01      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 3.97/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2526,plain,
% 3.97/1.01      ( arAF0_sP1_0_1(X0)
% 3.97/1.01      | ~ l1_pre_topc(X0)
% 3.97/1.01      | ~ l1_pre_topc(X1)
% 3.97/1.01      | ~ iProver_ARSWP_103 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_16]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3025,plain,
% 3.97/1.01      ( arAF0_sP1_0_1(X0) = iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(X0) != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2526]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3393,plain,
% 3.97/1.01      ( arAF0_sP1_0_1(X0) | ~ l1_pre_topc(X0) | ~ iProver_ARSWP_103 ),
% 3.97/1.01      inference(resolution,[status(thm)],[c_2526,c_21]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3394,plain,
% 3.97/1.01      ( arAF0_sP1_0_1(X0) = iProver_top
% 3.97/1.01      | l1_pre_topc(X0) != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_3393]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3826,plain,
% 3.97/1.01      ( arAF0_sP1_0_1(X0) = iProver_top
% 3.97/1.01      | l1_pre_topc(X0) != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3025,c_3394]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3833,plain,
% 3.97/1.01      ( arAF0_sP1_0_1(sK5) = iProver_top | iProver_ARSWP_103 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3041,c_3826]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_20,negated_conjecture,
% 3.97/1.01      ( m1_pre_topc(sK6,sK5) ),
% 3.97/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2528,negated_conjecture,
% 3.97/1.01      ( arAF0_m1_pre_topc_0_1(sK6) | ~ iProver_ARSWP_105 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_20]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3023,plain,
% 3.97/1.01      ( arAF0_m1_pre_topc_0_1(sK6) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2528]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5,plain,
% 3.97/1.01      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 3.97/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2515,plain,
% 3.97/1.01      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 3.97/1.01      | arAF0_sP0_0_1(X0)
% 3.97/1.01      | ~ arAF0_sP1_0_1(X1)
% 3.97/1.01      | ~ iProver_ARSWP_92 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3034,plain,
% 3.97/1.01      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | arAF0_sP1_0_1(X1) != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2515]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4089,plain,
% 3.97/1.01      ( arAF0_sP0_0_1(sK6) = iProver_top
% 3.97/1.01      | arAF0_sP1_0_1(X0) != iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3023,c_3034]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4381,plain,
% 3.97/1.01      ( arAF0_sP0_0_1(sK6) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3833,c_4089]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_15,plain,
% 3.97/1.01      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.97/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2525,plain,
% 3.97/1.01      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.97/1.01      | ~ arAF0_sP0_0_1(X0)
% 3.97/1.01      | ~ iProver_ARSWP_102 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_15]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3026,plain,
% 3.97/1.01      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2525]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4543,plain,
% 3.97/1.01      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4381,c_3026]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_19,negated_conjecture,
% 3.97/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.97/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3042,plain,
% 3.97/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3,plain,
% 3.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.97/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3044,plain,
% 3.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.97/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3367,plain,
% 3.97/1.01      ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3042,c_3044]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1,plain,
% 3.97/1.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.97/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2513,plain,
% 3.97/1.01      ( ~ r1_tarski(X0,X1) | ~ iProver_ARSWP_90 | arAF0_k2_xboole_0_0 = X1 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3036,plain,
% 3.97/1.01      ( arAF0_k2_xboole_0_0 = X0
% 3.97/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2513]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3508,plain,
% 3.97/1.01      ( u1_struct_0(sK6) = arAF0_k2_xboole_0_0
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3367,c_3036]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9,plain,
% 3.97/1.01      ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 3.97/1.01      | sP0(X0,X1)
% 3.97/1.01      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/1.01      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.97/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2519,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.97/1.01      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.97/1.01      | arAF0_sP0_0_1(X1)
% 3.97/1.01      | ~ iProver_ARSWP_96
% 3.97/1.01      | arAF0_r2_hidden_0 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3030,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2519]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6106,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3030,c_3044]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4,plain,
% 3.97/1.01      ( ~ sP1(X0,X1) | ~ sP0(X1,X0) | m1_pre_topc(X1,X0) ),
% 3.97/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2514,plain,
% 3.97/1.01      ( arAF0_m1_pre_topc_0_1(X0)
% 3.97/1.01      | ~ arAF0_sP0_0_1(X0)
% 3.97/1.01      | ~ arAF0_sP1_0_1(X1)
% 3.97/1.01      | ~ iProver_ARSWP_91 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_4]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3035,plain,
% 3.97/1.01      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) != iProver_top
% 3.97/1.01      | arAF0_sP1_0_1(X1) != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2514]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4202,plain,
% 3.97/1.01      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3833,c_3035]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6289,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_6106,c_4202]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_17,plain,
% 3.97/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.97/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2527,plain,
% 3.97/1.01      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 3.97/1.01      | ~ l1_pre_topc(X1)
% 3.97/1.01      | l1_pre_topc(X0)
% 3.97/1.01      | ~ iProver_ARSWP_104 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_17]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3024,plain,
% 3.97/1.01      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2527]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3453,plain,
% 3.97/1.01      ( ~ arAF0_m1_pre_topc_0_1(X0) | l1_pre_topc(X0) | ~ iProver_ARSWP_104 ),
% 3.97/1.01      inference(resolution,[status(thm)],[c_2527,c_21]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3454,plain,
% 3.97/1.01      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_3453]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3495,plain,
% 3.97/1.01      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3024,c_3454]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6932,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_6289,c_3495]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9135,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP1_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_6932,c_3826]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10538,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP1_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_9135]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_11079,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | arAF0_sP1_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_10538]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10542,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP1_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_9135,c_3036]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10851,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | arAF0_sP1_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_10542]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10,plain,
% 3.97/1.01      ( sP0(X0,X1)
% 3.97/1.01      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.97/1.01      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.97/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2520,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.97/1.01      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.97/1.01      | arAF0_sP0_0_1(X0)
% 3.97/1.01      | ~ iProver_ARSWP_97 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3029,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_97 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2520]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5180,plain,
% 3.97/1.01      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | r1_tarski(arAF0_sK2_0,u1_struct_0(X0)) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_97 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3029,c_3044]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5341,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_97 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_5180,c_3036]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7851,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_97 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_5341]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8632,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_97 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_7851,c_4202]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8949,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | l1_pre_topc(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_97 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_8632,c_3495]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10525,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | arAF0_sP1_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_97 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_8949,c_3826]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7,plain,
% 3.97/1.01      ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 3.97/1.01      | sP0(X0,X1)
% 3.97/1.01      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
% 3.97/1.01      | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) ),
% 3.97/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2517,plain,
% 3.97/1.01      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.97/1.01      | arAF0_sP0_0_1(X0)
% 3.97/1.01      | ~ iProver_ARSWP_94
% 3.97/1.01      | arAF0_r2_hidden_0
% 3.97/1.01      | arAF0_k9_subset_1_0 = arAF0_sK2_0 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3032,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_94 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2517]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5372,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_94 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_3032]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8143,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 3.97/1.01      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_94 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_5372,c_4202]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8328,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 3.97/1.01      | l1_pre_topc(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_94 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_8143,c_3495]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10279,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 3.97/1.01      | arAF0_sP1_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_94 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_8328,c_3826]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6099,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_3030]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6744,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_6099,c_4202]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7198,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_6744,c_3495]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10244,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP1_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_7198,c_3826]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8,plain,
% 3.97/1.01      ( r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
% 3.97/1.01      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 3.97/1.01      | sP0(X0,X1)
% 3.97/1.01      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.97/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2518,plain,
% 3.97/1.01      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.97/1.01      | arAF0_sP0_0_1(X0)
% 3.97/1.01      | ~ iProver_ARSWP_95
% 3.97/1.01      | arAF0_r2_hidden_0 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3031,plain,
% 3.97/1.01      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_95 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2518]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4857,plain,
% 3.97/1.01      ( arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_95 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_3031]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8102,plain,
% 3.97/1.01      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_95 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4857,c_4202]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8288,plain,
% 3.97/1.01      ( l1_pre_topc(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_95 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_8102,c_3495]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10013,plain,
% 3.97/1.01      ( arAF0_sP1_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_95 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_8288,c_3826]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4858,plain,
% 3.97/1.01      ( arAF0_k2_struct_0_0 = arAF0_k2_xboole_0_0
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_3036]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7550,plain,
% 3.97/1.01      ( r1_tarski(arAF0_k2_xboole_0_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4858,c_4543]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_0,plain,
% 3.97/1.01      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.97/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2512,plain,
% 3.97/1.01      ( r1_tarski(X0,X1)
% 3.97/1.01      | ~ r1_tarski(arAF0_k2_xboole_0_0,X1)
% 3.97/1.01      | ~ iProver_ARSWP_89 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3037,plain,
% 3.97/1.01      ( r1_tarski(X0,X1) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_xboole_0_0,X1) != iProver_top
% 3.97/1.01      | iProver_ARSWP_89 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2512]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8583,plain,
% 3.97/1.01      ( r1_tarski(X0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | iProver_ARSWP_89 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_7550,c_3037]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2,plain,
% 3.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.97/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3045,plain,
% 3.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.97/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_12,plain,
% 3.97/1.01      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.97/1.01      | ~ sP0(X1,X2)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/1.01      | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
% 3.97/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2522,plain,
% 3.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/1.01      | ~ arAF0_sP0_0_1(X1)
% 3.97/1.01      | ~ iProver_ARSWP_99
% 3.97/1.01      | ~ arAF0_r2_hidden_0
% 3.97/1.01      | arAF0_k9_subset_1_0 = X0 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3028,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = X0
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X1) != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2522]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5006,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = X0
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_3028]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5737,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = X0
% 3.97/1.01      | r1_tarski(X0,arAF0_k2_xboole_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3045,c_5006]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9480,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = X0
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | iProver_ARSWP_89 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_8583,c_5737]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9771,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = X0
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | iProver_ARSWP_89 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,[status(thm)],[c_9480,c_4381]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9137,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_6932,c_3036]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9641,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | l1_pre_topc(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_9137]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8585,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = arAF0_k2_xboole_0_0
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_7550,c_5737]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9619,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = arAF0_k2_xboole_0_0
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,[status(thm)],[c_8585,c_4381]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6101,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3030,c_4202]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7010,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_6101,c_3495]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9447,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP1_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_7010,c_3826]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9134,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_6932]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9206,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | l1_pre_topc(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_9134]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6934,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_6289,c_3036]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8990,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_6934]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6295,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_6106,c_3036]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7898,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | arAF0_sP0_0_1(X1) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_6295]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6930,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_6289]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7184,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_91 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_6930]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6287,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_6106]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6732,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK3_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_102 != iProver_top
% 3.97/1.01      | iProver_ARSWP_96 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4543,c_6287]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_14,plain,
% 3.97/1.01      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.97/1.01      | ~ sP0(X1,X2)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/1.01      | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) ),
% 3.97/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2524,plain,
% 3.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/1.01      | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.97/1.01      | ~ arAF0_sP0_0_1(X1)
% 3.97/1.01      | ~ iProver_ARSWP_101
% 3.97/1.01      | ~ arAF0_r2_hidden_0 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_14]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3027,plain,
% 3.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X1) != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2524]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4046,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3042,c_3027]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4232,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_4046]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5739,plain,
% 3.97/1.01      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4232,c_5006]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5780,plain,
% 3.97/1.01      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4381,c_5739]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5005,plain,
% 3.97/1.01      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 3.97/1.01      | arAF0_sP0_0_1(X0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4046,c_3028]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5510,plain,
% 3.97/1.01      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4381,c_5005]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5930,plain,
% 3.97/1.01      ( iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | arAF0_sK4_0 = arAF0_k9_subset_1_0
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_5780,c_4381,c_5510]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5931,plain,
% 3.97/1.01      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(renaming,[status(thm)],[c_5930]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5340,plain,
% 3.97/1.01      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | r1_tarski(arAF0_sK2_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(sK6) = iProver_top
% 3.97/1.01      | iProver_ARSWP_97 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_5180]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5179,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(sK6) = iProver_top
% 3.97/1.01      | iProver_ARSWP_97 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_3029]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5004,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = sK7
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3042,c_3028]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5172,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = sK7
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4381,c_5004]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5003,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 = X0
% 3.97/1.01      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X1) != iProver_top
% 3.97/1.01      | iProver_ARSWP_99 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3045,c_3028]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4233,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK4_0,u1_struct_0(X0)) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4046,c_3044]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4351,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4233,c_3036]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4693,plain,
% 3.97/1.01      ( u1_struct_0(X0) = arAF0_k2_xboole_0_0
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | iProver_ARSWP_92 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4381,c_4351]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4350,plain,
% 3.97/1.01      ( r1_tarski(arAF0_sK4_0,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(sK6) != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_4233]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4045,plain,
% 3.97/1.01      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.97/1.01      | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X2) != iProver_top
% 3.97/1.01      | iProver_ARSWP_101 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3045,c_3027]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3502,plain,
% 3.97/1.01      ( l1_pre_topc(sK6) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3023,c_3495]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3834,plain,
% 3.97/1.01      ( arAF0_sP1_0_1(sK6) = iProver_top
% 3.97/1.01      | iProver_ARSWP_105 != iProver_top
% 3.97/1.01      | iProver_ARSWP_104 != iProver_top
% 3.97/1.01      | iProver_ARSWP_103 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3502,c_3826]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3728,plain,
% 3.97/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_xboole_0_0)) = iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_3042]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3727,plain,
% 3.97/1.01      ( r1_tarski(sK7,arAF0_k2_xboole_0_0) = iProver_top
% 3.97/1.01      | iProver_ARSWP_90 != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3508,c_3367]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_18,negated_conjecture,
% 3.97/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.97/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3043,plain,
% 3.97/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3429,plain,
% 3.97/1.01      ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_3045,c_3043]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6,plain,
% 3.97/1.01      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.97/1.01      | ~ r2_hidden(sK2(X2,X1),u1_pre_topc(X2))
% 3.97/1.01      | sP0(X2,X1)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/1.01      | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
% 3.97/1.01      | k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)) != sK2(X2,X1) ),
% 3.97/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2516,plain,
% 3.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/1.01      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 3.97/1.01      | arAF0_sP0_0_1(X2)
% 3.97/1.01      | ~ iProver_ARSWP_93
% 3.97/1.01      | ~ arAF0_r2_hidden_0
% 3.97/1.01      | arAF0_k9_subset_1_0 != arAF0_sK2_0 ),
% 3.97/1.01      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3033,plain,
% 3.97/1.01      ( arAF0_k9_subset_1_0 != arAF0_sK2_0
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 3.97/1.01      | arAF0_sP0_0_1(X2) = iProver_top
% 3.97/1.01      | iProver_ARSWP_93 != iProver_top
% 3.97/1.01      | arAF0_r2_hidden_0 != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2516]) ).
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  % SZS output end Saturation for theBenchmark.p
% 3.97/1.01  
% 3.97/1.01  ------                               Statistics
% 3.97/1.01  
% 3.97/1.01  ------ Selected
% 3.97/1.01  
% 3.97/1.01  total_time:                             0.327
% 3.97/1.01  
%------------------------------------------------------------------------------
