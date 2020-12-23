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
% DateTime   : Thu Dec  3 12:16:38 EST 2020

% Result     : Theorem 15.53s
% Output     : CNFRefutation 15.53s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 367 expanded)
%              Number of clauses        :   77 ( 128 expanded)
%              Number of leaves         :   23 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          :  495 (1383 expanded)
%              Number of equality atoms :   95 ( 166 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) )
        & m1_pre_topc(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,sK7) )
      & l1_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    & m1_pre_topc(sK8,sK7)
    & l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f15,f38,f37,f36])).

fof(f65,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,plain,(
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

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = sK4(X0,X1)
              & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f17,f16])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f10])).

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
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

cnf(c_3889,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3893,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_6697,plain,
    ( ~ r2_hidden(X0,u1_struct_0(X1))
    | r2_hidden(X2,u1_struct_0(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_3889,c_3893])).

cnf(c_23,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_392,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_23,c_9])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_478,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_392,c_28])).

cnf(c_479,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_15520,plain,
    ( r2_hidden(X0,u1_struct_0(u1_struct_0(sK7)))
    | ~ r2_hidden(X1,u1_struct_0(k2_struct_0(sK7)))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_6697,c_479])).

cnf(c_3886,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6693,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_3889,c_3886])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_463,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK8 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_464,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_466,plain,
    ( l1_pre_topc(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_28])).

cnf(c_483,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_392,c_466])).

cnf(c_484,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_10862,plain,
    ( r2_hidden(u1_struct_0(sK8),X0)
    | ~ r2_hidden(k2_struct_0(sK8),X0) ),
    inference(resolution,[status(thm)],[c_6693,c_484])).

cnf(c_16229,plain,
    ( r2_hidden(X0,u1_struct_0(u1_struct_0(sK7)))
    | ~ r2_hidden(k2_struct_0(sK8),u1_struct_0(k2_struct_0(sK7)))
    | X0 != u1_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_15520,c_10862])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_406,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_22,c_11])).

cnf(c_410,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_24])).

cnf(c_411,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_410])).

cnf(c_452,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK8 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_27])).

cnf(c_453,plain,
    ( sP0(sK8,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_455,plain,
    ( sP0(sK8,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_28])).

cnf(c_982,plain,
    ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | sK8 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_455])).

cnf(c_983,plain,
    ( r1_tarski(k2_struct_0(sK8),k2_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_982])).

cnf(c_3890,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_6695,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r2_hidden(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_3889,c_3890])).

cnf(c_14020,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X1,k1_zfmisc_1(k2_struct_0(sK7)))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_6695,c_479])).

cnf(c_14510,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(k2_struct_0(sK8),k1_zfmisc_1(k2_struct_0(sK7)))
    | X0 != u1_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_14020,c_10862])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4529,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4448,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4460,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4563,plain,
    ( r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4448,c_4460])).

cnf(c_4564,plain,
    ( r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4563])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4644,plain,
    ( r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),sK9)
    | r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4643,plain,
    ( ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(u1_struct_0(sK7)))
    | r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4793,plain,
    ( r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r1_tarski(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5236,plain,
    ( r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))))
    | r1_tarski(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5235,plain,
    ( ~ r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),u1_struct_0(sK7))
    | r1_tarski(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5474,plain,
    ( sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))) = sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_3886])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5563,plain,
    ( ~ r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),X0)
    | r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ r1_tarski(X0,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7119,plain,
    ( ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X0))
    | r1_tarski(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_13194,plain,
    ( X0 != u1_struct_0(sK8)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_3890])).

cnf(c_7717,plain,
    ( ~ r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),X0)
    | r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_15292,plain,
    ( r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),X0)
    | ~ r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ r1_tarski(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),X0) ),
    inference(instantiation,[status(thm)],[c_7717])).

cnf(c_5381,plain,
    ( ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),X0)
    | r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7484,plain,
    ( r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),sK9)
    | ~ r1_tarski(sK9,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_5381])).

cnf(c_18066,plain,
    ( r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),sK9)
    | ~ r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_7484])).

cnf(c_27792,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | r1_tarski(X0,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4626,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_3889])).

cnf(c_4769,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r2_hidden(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_4626])).

cnf(c_5396,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X2))
    | sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))) != X0
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_4769])).

cnf(c_7602,plain,
    ( ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X0))
    | r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X1))
    | sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))) != sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7)))
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_5396])).

cnf(c_44671,plain,
    ( r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(u1_struct_0(sK8)))
    | sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))) != sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7)))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7602])).

cnf(c_45400,plain,
    ( ~ r2_hidden(k2_struct_0(sK8),k1_zfmisc_1(k2_struct_0(sK7)))
    | X0 != u1_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14510,c_25,c_4529,c_4564,c_4644,c_4643,c_4793,c_5236,c_5235,c_5474,c_5563,c_7119,c_13194,c_15292,c_18066,c_27792,c_44671])).

cnf(c_45418,plain,
    ( ~ r1_tarski(k2_struct_0(sK8),k2_struct_0(sK7))
    | X0 != u1_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_45400,c_5])).

cnf(c_45904,plain,
    ( X0 != u1_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16229,c_983,c_45418])).

cnf(c_3887,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5895,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_3887,c_3886])).

cnf(c_9861,plain,
    ( k2_struct_0(sK8) = u1_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_5895,c_484])).

cnf(c_47774,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_45904,c_9861])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:54:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.53/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.53/2.49  
% 15.53/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.53/2.49  
% 15.53/2.49  ------  iProver source info
% 15.53/2.49  
% 15.53/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.53/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.53/2.49  git: non_committed_changes: false
% 15.53/2.49  git: last_make_outside_of_git: false
% 15.53/2.49  
% 15.53/2.49  ------ 
% 15.53/2.49  ------ Parsing...
% 15.53/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.53/2.49  
% 15.53/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 15.53/2.49  
% 15.53/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.53/2.49  
% 15.53/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.53/2.49  ------ Proving...
% 15.53/2.49  ------ Problem Properties 
% 15.53/2.49  
% 15.53/2.49  
% 15.53/2.49  clauses                                 24
% 15.53/2.49  conjectures                             2
% 15.53/2.49  EPR                                     2
% 15.53/2.49  Horn                                    18
% 15.53/2.49  unary                                   5
% 15.53/2.49  binary                                  7
% 15.53/2.49  lits                                    66
% 15.53/2.49  lits eq                                 7
% 15.53/2.49  fd_pure                                 0
% 15.53/2.49  fd_pseudo                               0
% 15.53/2.49  fd_cond                                 0
% 15.53/2.49  fd_pseudo_cond                          2
% 15.53/2.49  AC symbols                              0
% 15.53/2.49  
% 15.53/2.49  ------ Input Options Time Limit: Unbounded
% 15.53/2.49  
% 15.53/2.49  
% 15.53/2.49  ------ 
% 15.53/2.49  Current options:
% 15.53/2.49  ------ 
% 15.53/2.49  
% 15.53/2.49  
% 15.53/2.49  
% 15.53/2.49  
% 15.53/2.49  ------ Proving...
% 15.53/2.49  
% 15.53/2.49  
% 15.53/2.49  % SZS status Theorem for theBenchmark.p
% 15.53/2.49  
% 15.53/2.49   Resolution empty clause
% 15.53/2.49  
% 15.53/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.53/2.49  
% 15.53/2.49  fof(f6,axiom,(
% 15.53/2.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.53/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.49  
% 15.53/2.49  fof(f13,plain,(
% 15.53/2.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.53/2.49    inference(ennf_transformation,[],[f6])).
% 15.53/2.49  
% 15.53/2.49  fof(f63,plain,(
% 15.53/2.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.53/2.49    inference(cnf_transformation,[],[f13])).
% 15.53/2.49  
% 15.53/2.49  fof(f4,axiom,(
% 15.53/2.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 15.53/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.49  
% 15.53/2.49  fof(f11,plain,(
% 15.53/2.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 15.53/2.49    inference(ennf_transformation,[],[f4])).
% 15.53/2.49  
% 15.53/2.49  fof(f49,plain,(
% 15.53/2.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 15.53/2.49    inference(cnf_transformation,[],[f11])).
% 15.53/2.49  
% 15.53/2.49  fof(f8,conjecture,(
% 15.53/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 15.53/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.49  
% 15.53/2.49  fof(f9,negated_conjecture,(
% 15.53/2.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 15.53/2.49    inference(negated_conjecture,[],[f8])).
% 15.53/2.49  
% 15.53/2.49  fof(f15,plain,(
% 15.53/2.49    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 15.53/2.49    inference(ennf_transformation,[],[f9])).
% 15.53/2.49  
% 15.53/2.49  fof(f38,plain,(
% 15.53/2.49    ( ! [X0,X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) => (~m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 15.53/2.49    introduced(choice_axiom,[])).
% 15.53/2.49  
% 15.53/2.49  fof(f37,plain,(
% 15.53/2.49    ( ! [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) => (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))) & m1_pre_topc(sK8,X0))) )),
% 15.53/2.49    introduced(choice_axiom,[])).
% 15.53/2.49  
% 15.53/2.49  fof(f36,plain,(
% 15.53/2.49    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,sK7)) & l1_pre_topc(sK7))),
% 15.53/2.49    introduced(choice_axiom,[])).
% 15.53/2.49  
% 15.53/2.49  fof(f39,plain,(
% 15.53/2.49    ((~m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))) & m1_pre_topc(sK8,sK7)) & l1_pre_topc(sK7)),
% 15.53/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f15,f38,f37,f36])).
% 15.53/2.49  
% 15.53/2.49  fof(f65,plain,(
% 15.53/2.49    l1_pre_topc(sK7)),
% 15.53/2.49    inference(cnf_transformation,[],[f39])).
% 15.53/2.49  
% 15.53/2.49  fof(f7,axiom,(
% 15.53/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 15.53/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.49  
% 15.53/2.49  fof(f14,plain,(
% 15.53/2.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.53/2.49    inference(ennf_transformation,[],[f7])).
% 15.53/2.49  
% 15.53/2.49  fof(f64,plain,(
% 15.53/2.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.53/2.49    inference(cnf_transformation,[],[f14])).
% 15.53/2.49  
% 15.53/2.49  fof(f66,plain,(
% 15.53/2.49    m1_pre_topc(sK8,sK7)),
% 15.53/2.49    inference(cnf_transformation,[],[f39])).
% 15.53/2.49  
% 15.53/2.49  fof(f16,plain,(
% 15.53/2.49    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 15.53/2.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 15.53/2.49  
% 15.53/2.49  fof(f29,plain,(
% 15.53/2.49    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 15.53/2.49    inference(nnf_transformation,[],[f16])).
% 15.53/2.49  
% 15.53/2.49  fof(f30,plain,(
% 15.53/2.49    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 15.53/2.49    inference(flattening,[],[f29])).
% 15.53/2.49  
% 15.53/2.49  fof(f31,plain,(
% 15.53/2.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 15.53/2.49    inference(rectify,[],[f30])).
% 15.53/2.49  
% 15.53/2.49  fof(f34,plain,(
% 15.53/2.49    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 15.53/2.49    introduced(choice_axiom,[])).
% 15.53/2.49  
% 15.53/2.49  fof(f33,plain,(
% 15.53/2.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 15.53/2.49    introduced(choice_axiom,[])).
% 15.53/2.49  
% 15.53/2.49  fof(f32,plain,(
% 15.53/2.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.53/2.49    introduced(choice_axiom,[])).
% 15.53/2.49  
% 15.53/2.49  fof(f35,plain,(
% 15.53/2.49    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 15.53/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).
% 15.53/2.49  
% 15.53/2.49  fof(f52,plain,(
% 15.53/2.49    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 15.53/2.49    inference(cnf_transformation,[],[f35])).
% 15.53/2.49  
% 15.53/2.49  fof(f5,axiom,(
% 15.53/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 15.53/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.49  
% 15.53/2.49  fof(f12,plain,(
% 15.53/2.49    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.53/2.49    inference(ennf_transformation,[],[f5])).
% 15.53/2.49  
% 15.53/2.49  fof(f17,plain,(
% 15.53/2.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 15.53/2.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 15.53/2.49  
% 15.53/2.49  fof(f18,plain,(
% 15.53/2.49    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.53/2.49    inference(definition_folding,[],[f12,f17,f16])).
% 15.53/2.49  
% 15.53/2.49  fof(f62,plain,(
% 15.53/2.49    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 15.53/2.49    inference(cnf_transformation,[],[f18])).
% 15.53/2.49  
% 15.53/2.49  fof(f28,plain,(
% 15.53/2.49    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 15.53/2.49    inference(nnf_transformation,[],[f17])).
% 15.53/2.49  
% 15.53/2.49  fof(f50,plain,(
% 15.53/2.49    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 15.53/2.49    inference(cnf_transformation,[],[f28])).
% 15.53/2.49  
% 15.53/2.49  fof(f68,plain,(
% 15.53/2.49    ~m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))),
% 15.53/2.49    inference(cnf_transformation,[],[f39])).
% 15.53/2.49  
% 15.53/2.49  fof(f3,axiom,(
% 15.53/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.53/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.49  
% 15.53/2.49  fof(f27,plain,(
% 15.53/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.53/2.49    inference(nnf_transformation,[],[f3])).
% 15.53/2.49  
% 15.53/2.49  fof(f48,plain,(
% 15.53/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.53/2.49    inference(cnf_transformation,[],[f27])).
% 15.53/2.49  
% 15.53/2.49  fof(f67,plain,(
% 15.53/2.49    m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))),
% 15.53/2.49    inference(cnf_transformation,[],[f39])).
% 15.53/2.49  
% 15.53/2.49  fof(f47,plain,(
% 15.53/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.53/2.49    inference(cnf_transformation,[],[f27])).
% 15.53/2.49  
% 15.53/2.49  fof(f1,axiom,(
% 15.53/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.53/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.49  
% 15.53/2.49  fof(f10,plain,(
% 15.53/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.53/2.49    inference(ennf_transformation,[],[f1])).
% 15.53/2.49  
% 15.53/2.49  fof(f19,plain,(
% 15.53/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.53/2.49    inference(nnf_transformation,[],[f10])).
% 15.53/2.49  
% 15.53/2.49  fof(f20,plain,(
% 15.53/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.53/2.49    inference(rectify,[],[f19])).
% 15.53/2.49  
% 15.53/2.49  fof(f21,plain,(
% 15.53/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 15.53/2.49    introduced(choice_axiom,[])).
% 15.53/2.49  
% 15.53/2.49  fof(f22,plain,(
% 15.53/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.53/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 15.53/2.49  
% 15.53/2.49  fof(f41,plain,(
% 15.53/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 15.53/2.49    inference(cnf_transformation,[],[f22])).
% 15.53/2.49  
% 15.53/2.49  fof(f42,plain,(
% 15.53/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 15.53/2.49    inference(cnf_transformation,[],[f22])).
% 15.53/2.49  
% 15.53/2.49  fof(f2,axiom,(
% 15.53/2.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 15.53/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.49  
% 15.53/2.49  fof(f23,plain,(
% 15.53/2.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.53/2.49    inference(nnf_transformation,[],[f2])).
% 15.53/2.49  
% 15.53/2.49  fof(f24,plain,(
% 15.53/2.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.53/2.49    inference(rectify,[],[f23])).
% 15.53/2.49  
% 15.53/2.49  fof(f25,plain,(
% 15.53/2.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 15.53/2.49    introduced(choice_axiom,[])).
% 15.53/2.49  
% 15.53/2.49  fof(f26,plain,(
% 15.53/2.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.53/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 15.53/2.49  
% 15.53/2.49  fof(f44,plain,(
% 15.53/2.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 15.53/2.49    inference(cnf_transformation,[],[f26])).
% 15.53/2.49  
% 15.53/2.49  fof(f69,plain,(
% 15.53/2.49    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 15.53/2.49    inference(equality_resolution,[],[f44])).
% 15.53/2.49  
% 15.53/2.49  fof(f40,plain,(
% 15.53/2.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.53/2.49    inference(cnf_transformation,[],[f22])).
% 15.53/2.49  
% 15.53/2.49  fof(f43,plain,(
% 15.53/2.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 15.53/2.49    inference(cnf_transformation,[],[f26])).
% 15.53/2.49  
% 15.53/2.49  fof(f70,plain,(
% 15.53/2.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 15.53/2.49    inference(equality_resolution,[],[f43])).
% 15.53/2.49  
% 15.53/2.49  cnf(c_3889,plain,
% 15.53/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.53/2.49      theory(equality) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_3893,plain,
% 15.53/2.49      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 15.53/2.49      theory(equality) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_6697,plain,
% 15.53/2.49      ( ~ r2_hidden(X0,u1_struct_0(X1))
% 15.53/2.49      | r2_hidden(X2,u1_struct_0(X3))
% 15.53/2.49      | X2 != X0
% 15.53/2.49      | X3 != X1 ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_3889,c_3893]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_23,plain,
% 15.53/2.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 15.53/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_9,plain,
% 15.53/2.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 15.53/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_392,plain,
% 15.53/2.49      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_23,c_9]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_28,negated_conjecture,
% 15.53/2.49      ( l1_pre_topc(sK7) ),
% 15.53/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_478,plain,
% 15.53/2.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK7 != X0 ),
% 15.53/2.49      inference(resolution_lifted,[status(thm)],[c_392,c_28]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_479,plain,
% 15.53/2.49      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 15.53/2.49      inference(unflattening,[status(thm)],[c_478]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_15520,plain,
% 15.53/2.49      ( r2_hidden(X0,u1_struct_0(u1_struct_0(sK7)))
% 15.53/2.49      | ~ r2_hidden(X1,u1_struct_0(k2_struct_0(sK7)))
% 15.53/2.49      | X0 != X1 ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_6697,c_479]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_3886,plain,( X0 = X0 ),theory(equality) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_6693,plain,
% 15.53/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_3889,c_3886]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_24,plain,
% 15.53/2.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 15.53/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_27,negated_conjecture,
% 15.53/2.49      ( m1_pre_topc(sK8,sK7) ),
% 15.53/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_463,plain,
% 15.53/2.49      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK8 != X1 | sK7 != X0 ),
% 15.53/2.49      inference(resolution_lifted,[status(thm)],[c_24,c_27]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_464,plain,
% 15.53/2.49      ( l1_pre_topc(sK8) | ~ l1_pre_topc(sK7) ),
% 15.53/2.49      inference(unflattening,[status(thm)],[c_463]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_466,plain,
% 15.53/2.49      ( l1_pre_topc(sK8) ),
% 15.53/2.49      inference(global_propositional_subsumption,[status(thm)],[c_464,c_28]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_483,plain,
% 15.53/2.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK8 != X0 ),
% 15.53/2.49      inference(resolution_lifted,[status(thm)],[c_392,c_466]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_484,plain,
% 15.53/2.49      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 15.53/2.49      inference(unflattening,[status(thm)],[c_483]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_10862,plain,
% 15.53/2.49      ( r2_hidden(u1_struct_0(sK8),X0) | ~ r2_hidden(k2_struct_0(sK8),X0) ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_6693,c_484]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_16229,plain,
% 15.53/2.49      ( r2_hidden(X0,u1_struct_0(u1_struct_0(sK7)))
% 15.53/2.49      | ~ r2_hidden(k2_struct_0(sK8),u1_struct_0(k2_struct_0(sK7)))
% 15.53/2.49      | X0 != u1_struct_0(sK8) ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_15520,c_10862]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_21,plain,
% 15.53/2.49      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 15.53/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_22,plain,
% 15.53/2.49      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 15.53/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_11,plain,
% 15.53/2.49      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 15.53/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_406,plain,
% 15.53/2.49      ( sP0(X0,X1)
% 15.53/2.49      | ~ m1_pre_topc(X0,X1)
% 15.53/2.49      | ~ l1_pre_topc(X1)
% 15.53/2.49      | ~ l1_pre_topc(X0) ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_22,c_11]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_410,plain,
% 15.53/2.49      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 15.53/2.49      inference(global_propositional_subsumption,[status(thm)],[c_406,c_24]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_411,plain,
% 15.53/2.49      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 15.53/2.49      inference(renaming,[status(thm)],[c_410]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_452,plain,
% 15.53/2.49      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK8 != X0 | sK7 != X1 ),
% 15.53/2.49      inference(resolution_lifted,[status(thm)],[c_411,c_27]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_453,plain,
% 15.53/2.49      ( sP0(sK8,sK7) | ~ l1_pre_topc(sK7) ),
% 15.53/2.49      inference(unflattening,[status(thm)],[c_452]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_455,plain,
% 15.53/2.49      ( sP0(sK8,sK7) ),
% 15.53/2.49      inference(global_propositional_subsumption,[status(thm)],[c_453,c_28]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_982,plain,
% 15.53/2.49      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | sK8 != X0 | sK7 != X1 ),
% 15.53/2.49      inference(resolution_lifted,[status(thm)],[c_21,c_455]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_983,plain,
% 15.53/2.49      ( r1_tarski(k2_struct_0(sK8),k2_struct_0(sK7)) ),
% 15.53/2.49      inference(unflattening,[status(thm)],[c_982]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_3890,plain,
% 15.53/2.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 15.53/2.49      theory(equality) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_6695,plain,
% 15.53/2.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 15.53/2.49      | r2_hidden(X2,k1_zfmisc_1(X3))
% 15.53/2.49      | X2 != X0
% 15.53/2.49      | X3 != X1 ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_3889,c_3890]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_14020,plain,
% 15.53/2.49      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 15.53/2.49      | ~ r2_hidden(X1,k1_zfmisc_1(k2_struct_0(sK7)))
% 15.53/2.49      | X0 != X1 ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_6695,c_479]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_14510,plain,
% 15.53/2.49      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 15.53/2.49      | ~ r2_hidden(k2_struct_0(sK8),k1_zfmisc_1(k2_struct_0(sK7)))
% 15.53/2.49      | X0 != u1_struct_0(sK8) ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_14020,c_10862]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_25,negated_conjecture,
% 15.53/2.49      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
% 15.53/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_7,plain,
% 15.53/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.53/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_4529,plain,
% 15.53/2.49      ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 15.53/2.49      | ~ r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_26,negated_conjecture,
% 15.53/2.49      ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
% 15.53/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_4448,plain,
% 15.53/2.49      ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
% 15.53/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_8,plain,
% 15.53/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.53/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_4460,plain,
% 15.53/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.53/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.53/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_4563,plain,
% 15.53/2.49      ( r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 15.53/2.49      inference(superposition,[status(thm)],[c_4448,c_4460]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_4564,plain,
% 15.53/2.49      ( r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 15.53/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_4563]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_1,plain,
% 15.53/2.49      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.53/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_4644,plain,
% 15.53/2.49      ( r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),sK9)
% 15.53/2.49      | r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_0,plain,
% 15.53/2.49      ( ~ r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.53/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_4643,plain,
% 15.53/2.49      ( ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(u1_struct_0(sK7)))
% 15.53/2.49      | r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_5,plain,
% 15.53/2.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.53/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_4793,plain,
% 15.53/2.49      ( r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(u1_struct_0(sK7)))
% 15.53/2.49      | ~ r1_tarski(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_5]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_5236,plain,
% 15.53/2.49      ( r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))))
% 15.53/2.49      | r1_tarski(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_5235,plain,
% 15.53/2.49      ( ~ r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),u1_struct_0(sK7))
% 15.53/2.49      | r1_tarski(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_5474,plain,
% 15.53/2.49      ( sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))) = sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_3886]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_2,plain,
% 15.53/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.53/2.49      inference(cnf_transformation,[],[f40]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_5563,plain,
% 15.53/2.49      ( ~ r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),X0)
% 15.53/2.49      | r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),u1_struct_0(sK7))
% 15.53/2.49      | ~ r1_tarski(X0,u1_struct_0(sK7)) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_6,plain,
% 15.53/2.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.53/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_7119,plain,
% 15.53/2.49      ( ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X0))
% 15.53/2.49      | r1_tarski(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),X0) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_6]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_13194,plain,
% 15.53/2.49      ( X0 != u1_struct_0(sK8)
% 15.53/2.49      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK8)) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_3890]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_7717,plain,
% 15.53/2.49      ( ~ r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),X0)
% 15.53/2.49      | r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),X1)
% 15.53/2.49      | ~ r1_tarski(X0,X1) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_15292,plain,
% 15.53/2.49      ( r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),X0)
% 15.53/2.49      | ~ r2_hidden(sK2(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),u1_struct_0(sK7)),sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))))
% 15.53/2.49      | ~ r1_tarski(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),X0) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_7717]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_5381,plain,
% 15.53/2.49      ( ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),X0)
% 15.53/2.49      | r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X1))
% 15.53/2.49      | ~ r1_tarski(X0,k1_zfmisc_1(X1)) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_7484,plain,
% 15.53/2.49      ( r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X0))
% 15.53/2.49      | ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),sK9)
% 15.53/2.49      | ~ r1_tarski(sK9,k1_zfmisc_1(X0)) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_5381]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_18066,plain,
% 15.53/2.49      ( r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(u1_struct_0(sK8)))
% 15.53/2.49      | ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),sK9)
% 15.53/2.49      | ~ r1_tarski(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_7484]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_27792,plain,
% 15.53/2.49      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 15.53/2.49      | r1_tarski(X0,u1_struct_0(sK7)) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_6]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_4626,plain,
% 15.53/2.49      ( r2_hidden(X0,X1)
% 15.53/2.49      | ~ r2_hidden(X2,k1_zfmisc_1(X3))
% 15.53/2.49      | X0 != X2
% 15.53/2.49      | X1 != k1_zfmisc_1(X3) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_3889]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_4769,plain,
% 15.53/2.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 15.53/2.49      | r2_hidden(X2,k1_zfmisc_1(X3))
% 15.53/2.49      | X2 != X0
% 15.53/2.49      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_4626]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_5396,plain,
% 15.53/2.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 15.53/2.49      | r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X2))
% 15.53/2.49      | sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))) != X0
% 15.53/2.49      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_4769]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_7602,plain,
% 15.53/2.49      ( ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X0))
% 15.53/2.49      | r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X1))
% 15.53/2.49      | sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))) != sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7)))
% 15.53/2.49      | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_5396]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_44671,plain,
% 15.53/2.49      ( r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(X0))
% 15.53/2.49      | ~ r2_hidden(sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))),k1_zfmisc_1(u1_struct_0(sK8)))
% 15.53/2.49      | sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7))) != sK2(sK9,k1_zfmisc_1(u1_struct_0(sK7)))
% 15.53/2.49      | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK8)) ),
% 15.53/2.49      inference(instantiation,[status(thm)],[c_7602]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_45400,plain,
% 15.53/2.49      ( ~ r2_hidden(k2_struct_0(sK8),k1_zfmisc_1(k2_struct_0(sK7)))
% 15.53/2.49      | X0 != u1_struct_0(sK8) ),
% 15.53/2.49      inference(global_propositional_subsumption,
% 15.53/2.49                [status(thm)],
% 15.53/2.49                [c_14510,c_25,c_4529,c_4564,c_4644,c_4643,c_4793,c_5236,
% 15.53/2.49                 c_5235,c_5474,c_5563,c_7119,c_13194,c_15292,c_18066,c_27792,
% 15.53/2.49                 c_44671]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_45418,plain,
% 15.53/2.49      ( ~ r1_tarski(k2_struct_0(sK8),k2_struct_0(sK7))
% 15.53/2.49      | X0 != u1_struct_0(sK8) ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_45400,c_5]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_45904,plain,
% 15.53/2.49      ( X0 != u1_struct_0(sK8) ),
% 15.53/2.49      inference(global_propositional_subsumption,
% 15.53/2.49                [status(thm)],
% 15.53/2.49                [c_16229,c_983,c_45418]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_3887,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_5895,plain,
% 15.53/2.49      ( X0 != X1 | X1 = X0 ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_3887,c_3886]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_9861,plain,
% 15.53/2.49      ( k2_struct_0(sK8) = u1_struct_0(sK8) ),
% 15.53/2.49      inference(resolution,[status(thm)],[c_5895,c_484]) ).
% 15.53/2.49  
% 15.53/2.49  cnf(c_47774,plain,
% 15.53/2.49      ( $false ),
% 15.53/2.49      inference(backward_subsumption_resolution,[status(thm)],[c_45904,c_9861]) ).
% 15.53/2.49  
% 15.53/2.49  
% 15.53/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.53/2.49  
% 15.53/2.49  ------                               Statistics
% 15.53/2.49  
% 15.53/2.49  ------ Selected
% 15.53/2.49  
% 15.53/2.49  total_time:                             1.563
% 15.53/2.49  
%------------------------------------------------------------------------------
