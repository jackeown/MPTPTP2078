%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:28 EST 2020

% Result     : CounterSatisfiable 7.51s
% Output     : Saturation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  324 (8571 expanded)
%              Number of clauses        :  273 (3332 expanded)
%              Number of leaves         :   20 (2401 expanded)
%              Depth                    :   18
%              Number of atoms          : 1671 (38100 expanded)
%              Number of equality atoms : 1224 (7894 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
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
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
        & m1_pre_topc(sK6,X0) ) ) ),
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
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,sK5) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_pre_topc(sK6,sK5)
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f16,f31,f30,f29])).

fof(f54,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(nnf_transformation,[],[f17])).

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
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f27,f26,f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(definition_folding,[],[f14,f18,f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1)
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_258,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3164,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3166,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3495,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_3166])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2612,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ iProver_ARSWP_91
    | arAF0_k3_xboole_0_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_3159,plain,
    ( arAF0_k3_xboole_0_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2612])).

cnf(c_3661,plain,
    ( arAF0_k3_xboole_0_0 = sK7
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_3159])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_159,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_160,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_159])).

cnf(c_204,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_160])).

cnf(c_2628,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ iProver_ARSWP_107 ),
    inference(arg_filter_abstr,[status(unp)],[c_204])).

cnf(c_3145,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | iProver_ARSWP_107 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2628])).

cnf(c_3655,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_107 != iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_3145])).

cnf(c_3895,plain,
    ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_107 != iProver_top ),
    inference(superposition,[status(thm)],[c_3655,c_3166])).

cnf(c_4001,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3895,c_3159])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2618,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_97
    | arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_3153,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2618])).

cnf(c_6706,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_3166])).

cnf(c_6901,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6706,c_3145])).

cnf(c_11490,plain,
    ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_3166])).

cnf(c_11550,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_11490])).

cnf(c_14147,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_11550])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3163,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2625,plain,
    ( arAF0_sP1_0_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ iProver_ARSWP_104 ),
    inference(arg_filter_abstr,[status(unp)],[c_17])).

cnf(c_3148,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2625])).

cnf(c_3521,plain,
    ( arAF0_sP1_0_1(X0)
    | ~ l1_pre_topc(X0)
    | ~ iProver_ARSWP_104 ),
    inference(resolution,[status(thm)],[c_2625,c_22])).

cnf(c_3522,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3521])).

cnf(c_4283,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3148,c_3522])).

cnf(c_4290,plain,
    ( arAF0_sP1_0_1(sK5) = iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_3163,c_4283])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2613,plain,
    ( arAF0_m1_pre_topc_0_1(X0)
    | ~ arAF0_sP0_0_1(X0)
    | ~ arAF0_sP1_0_1(X1)
    | ~ iProver_ARSWP_92 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_3158,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | arAF0_sP1_0_1(X1) != iProver_top
    | iProver_ARSWP_92 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2613])).

cnf(c_4421,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_92 != iProver_top ),
    inference(superposition,[status(thm)],[c_4290,c_3158])).

cnf(c_14429,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14147,c_4421])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2626,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_105 ),
    inference(arg_filter_abstr,[status(unp)],[c_18])).

cnf(c_3147,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2626])).

cnf(c_3605,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_105 ),
    inference(resolution,[status(thm)],[c_2626,c_22])).

cnf(c_3606,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3605])).

cnf(c_3804,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3147,c_3606])).

cnf(c_14841,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14429,c_3804])).

cnf(c_17508,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14841,c_4283])).

cnf(c_3167,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3165,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3581,plain,
    ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_3165])).

cnf(c_18819,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17508,c_3581])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2627,negated_conjecture,
    ( arAF0_m1_pre_topc_0_1(sK6)
    | ~ iProver_ARSWP_106 ),
    inference(arg_filter_abstr,[status(unp)],[c_21])).

cnf(c_3146,plain,
    ( arAF0_m1_pre_topc_0_1(sK6) = iProver_top
    | iProver_ARSWP_106 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2627])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2614,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | arAF0_sP0_0_1(X0)
    | ~ arAF0_sP1_0_1(X1)
    | ~ iProver_ARSWP_93 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_3157,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | arAF0_sP1_0_1(X1) != iProver_top
    | iProver_ARSWP_93 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2614])).

cnf(c_4412,plain,
    ( arAF0_sP0_0_1(sK6) = iProver_top
    | arAF0_sP1_0_1(X0) != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_93 != iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_3157])).

cnf(c_4535,plain,
    ( arAF0_sP0_0_1(sK6) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_93 != iProver_top ),
    inference(superposition,[status(thm)],[c_4290,c_4412])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2624,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_103 ),
    inference(arg_filter_abstr,[status(unp)],[c_16])).

cnf(c_3149,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | iProver_ARSWP_103 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2624])).

cnf(c_4742,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top ),
    inference(superposition,[status(thm)],[c_4535,c_3149])).

cnf(c_14437,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14147,c_3581])).

cnf(c_14571,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_14437])).

cnf(c_14792,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14571,c_4421])).

cnf(c_15061,plain,
    ( l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14792,c_3804])).

cnf(c_18105,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15061,c_4283])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_205,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_160])).

cnf(c_2629,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ iProver_ARSWP_108
    | arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_205])).

cnf(c_3144,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0
    | r1_tarski(X0,X1) != iProver_top
    | iProver_ARSWP_108 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2629])).

cnf(c_8214,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_108 != iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_3144])).

cnf(c_11481,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_6901])).

cnf(c_12530,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_11481,c_4421])).

cnf(c_13718,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_12530,c_3804])).

cnf(c_17928,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_13718,c_4283])).

cnf(c_17511,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14841,c_3581])).

cnf(c_6895,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6706,c_4421])).

cnf(c_7435,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6895,c_3804])).

cnf(c_15219,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7435,c_4283])).

cnf(c_17146,plain,
    ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15219,c_3159])).

cnf(c_17221,plain,
    ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_17146])).

cnf(c_17148,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15219,c_3145])).

cnf(c_11549,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_11490])).

cnf(c_12302,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_11549,c_4421])).

cnf(c_13588,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_12302,c_3804])).

cnf(c_16934,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_13588,c_4283])).

cnf(c_11,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2619,plain,
    ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_98 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_3152,plain,
    ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2619])).

cnf(c_4526,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_sK2_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(superposition,[status(thm)],[c_3152,c_3166])).

cnf(c_5351,plain,
    ( arAF0_sK2_0 = arAF0_k3_xboole_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_3159])).

cnf(c_9864,plain,
    ( arAF0_sK2_0 = arAF0_k3_xboole_0_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_5351])).

cnf(c_15756,plain,
    ( arAF0_sK2_0 = arAF0_k3_xboole_0_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_9864,c_4421])).

cnf(c_15855,plain,
    ( arAF0_sK2_0 = arAF0_k3_xboole_0_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_15756,c_3804])).

cnf(c_16918,plain,
    ( arAF0_sK2_0 = arAF0_k3_xboole_0_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_15855,c_4283])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2616,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_95
    | arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 = arAF0_sK2_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_3155,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_95 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2616])).

cnf(c_5524,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_95 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_3155])).

cnf(c_14104,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_95 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5524,c_4421])).

cnf(c_14647,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_95 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14104,c_3804])).

cnf(c_16797,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_95 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14647,c_4283])).

cnf(c_11552,plain,
    ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_11490,c_4421])).

cnf(c_13349,plain,
    ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_11552,c_3804])).

cnf(c_16592,plain,
    ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_13349,c_4283])).

cnf(c_9,plain,
    ( r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2617,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_96
    | arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_3154,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_96 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2617])).

cnf(c_4866,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_3154])).

cnf(c_11320,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4866,c_4421])).

cnf(c_12491,plain,
    ( l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_11320,c_3804])).

cnf(c_16575,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_96 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_12491,c_4283])).

cnf(c_4865,plain,
    ( arAF0_k2_struct_0_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_3159])).

cnf(c_5107,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_4742])).

cnf(c_6101,plain,
    ( r1_tarski(sK7,sK7) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_5107])).

cnf(c_6141,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_6101,c_3145])).

cnf(c_12793,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_6141])).

cnf(c_6640,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(sK7))
    | ~ r1_tarski(arAF0_k3_xboole_0_0,sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6641,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
    | r1_tarski(arAF0_k3_xboole_0_0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6640])).

cnf(c_12794,plain,
    ( r1_tarski(arAF0_k9_subset_1_0,sK7) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_6141,c_3166])).

cnf(c_12938,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,sK7) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_12794])).

cnf(c_3403,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_4,c_20])).

cnf(c_4545,plain,
    ( ~ iProver_ARSWP_91
    | arAF0_k3_xboole_0_0 = sK7 ),
    inference(resolution,[status(thm)],[c_2612,c_3403])).

cnf(c_272,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4578,plain,
    ( r1_tarski(X0,arAF0_k3_xboole_0_0)
    | ~ r1_tarski(X1,sK7)
    | ~ iProver_ARSWP_91
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_4545,c_272])).

cnf(c_271,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_270,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3747,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_271,c_270])).

cnf(c_4555,plain,
    ( ~ iProver_ARSWP_91
    | sK7 = arAF0_k3_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_4545,c_3747])).

cnf(c_6202,plain,
    ( ~ r1_tarski(arAF0_k3_xboole_0_0,sK7)
    | r1_tarski(sK7,arAF0_k3_xboole_0_0)
    | ~ iProver_ARSWP_91 ),
    inference(resolution,[status(thm)],[c_4578,c_4555])).

cnf(c_4345,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_272,c_270])).

cnf(c_5794,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,X0)
    | ~ r1_tarski(sK7,X0)
    | ~ iProver_ARSWP_91 ),
    inference(resolution,[status(thm)],[c_4345,c_4545])).

cnf(c_6573,plain,
    ( r1_tarski(sK7,arAF0_k3_xboole_0_0)
    | ~ r1_tarski(sK7,sK7)
    | ~ iProver_ARSWP_91 ),
    inference(resolution,[status(thm)],[c_6202,c_5794])).

cnf(c_6574,plain,
    ( r1_tarski(sK7,arAF0_k3_xboole_0_0) = iProver_top
    | r1_tarski(sK7,sK7) != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6573])).

cnf(c_4615,plain,
    ( ~ r1_tarski(X0,arAF0_k3_xboole_0_0)
    | r1_tarski(X1,sK7)
    | ~ iProver_ARSWP_91
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_4555,c_272])).

cnf(c_12609,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,sK7)
    | ~ r1_tarski(sK7,arAF0_k3_xboole_0_0)
    | ~ iProver_ARSWP_91 ),
    inference(resolution,[status(thm)],[c_4615,c_4545])).

cnf(c_12610,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,sK7) = iProver_top
    | r1_tarski(sK7,arAF0_k3_xboole_0_0) != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12609])).

cnf(c_13172,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,sK7) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12938,c_6101,c_6574,c_12610])).

cnf(c_16431,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12793,c_6101,c_6574,c_6641,c_12610])).

cnf(c_5352,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_3145])).

cnf(c_9623,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_5352])).

cnf(c_16258,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_9623])).

cnf(c_6702,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_4421])).

cnf(c_7512,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6702,c_3804])).

cnf(c_16228,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7512,c_4283])).

cnf(c_4867,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_3145])).

cnf(c_8302,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_4867])).

cnf(c_9412,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_8302])).

cnf(c_5882,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | ~ r1_tarski(sK7,arAF0_k2_struct_0_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5883,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | r1_tarski(sK7,arAF0_k2_struct_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5882])).

cnf(c_6309,plain,
    ( r1_tarski(arAF0_k9_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top ),
    inference(superposition,[status(thm)],[c_4867,c_3166])).

cnf(c_8300,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_6309])).

cnf(c_9172,plain,
    ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_8300])).

cnf(c_25,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2520,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_tarski(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2521,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2520])).

cnf(c_3450,plain,
    ( ~ r1_tarski(sK7,u1_struct_0(sK6))
    | ~ iProver_ARSWP_91
    | arAF0_k3_xboole_0_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_3451,plain,
    ( arAF0_k3_xboole_0_0 = sK7
    | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3450])).

cnf(c_4556,plain,
    ( sK7 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_91 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4555])).

cnf(c_8197,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK7,arAF0_k3_xboole_0_0)
    | X1 != arAF0_k3_xboole_0_0
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_8626,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(sK7,arAF0_k3_xboole_0_0)
    | X0 != sK7
    | arAF0_k2_struct_0_0 != arAF0_k3_xboole_0_0 ),
    inference(instantiation,[status(thm)],[c_8197])).

cnf(c_8829,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(sK7,arAF0_k3_xboole_0_0)
    | arAF0_k2_struct_0_0 != arAF0_k3_xboole_0_0
    | arAF0_k3_xboole_0_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_8626])).

cnf(c_8830,plain,
    ( arAF0_k2_struct_0_0 != arAF0_k3_xboole_0_0
    | arAF0_k3_xboole_0_0 != sK7
    | r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
    | r1_tarski(sK7,arAF0_k3_xboole_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8829])).

cnf(c_5645,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
    | X1 != arAF0_k2_struct_0_0
    | X0 != arAF0_k3_xboole_0_0 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_7244,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k3_xboole_0_0
    | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_5645])).

cnf(c_7245,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k3_xboole_0_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7244])).

cnf(c_9559,plain,
    ( ~ r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
    | r1_tarski(sK7,arAF0_k2_struct_0_0)
    | sK7 != arAF0_k3_xboole_0_0 ),
    inference(instantiation,[status(thm)],[c_7245])).

cnf(c_9560,plain,
    ( sK7 != arAF0_k3_xboole_0_0
    | r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9559])).

cnf(c_10124,plain,
    ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9172,c_25,c_2521,c_3451,c_4556,c_4865,c_6101,c_6574,c_8830,c_9560])).

cnf(c_10151,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9412,c_25,c_2521,c_3451,c_4556,c_4865,c_5883,c_6101,c_6574,c_8830,c_9560])).

cnf(c_10161,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k3_xboole_0_0)) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_10151])).

cnf(c_15469,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_10161])).

cnf(c_15220,plain,
    ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7435,c_3159])).

cnf(c_15291,plain,
    ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_15220])).

cnf(c_15222,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7435,c_3145])).

cnf(c_14844,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14429,c_3581])).

cnf(c_7436,plain,
    ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6895,c_3159])).

cnf(c_14281,plain,
    ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_7436])).

cnf(c_6307,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_4867])).

cnf(c_5646,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | ~ r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5647,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5646])).

cnf(c_7917,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_6309])).

cnf(c_3699,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k2_struct_0_0
    | X1 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_4250,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k2_struct_0_0
    | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_3699])).

cnf(c_4251,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k2_struct_0_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4250])).

cnf(c_4692,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
    | arAF0_k3_xboole_0_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_4251])).

cnf(c_4693,plain,
    ( arAF0_k3_xboole_0_0 != arAF0_k2_struct_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4692])).

cnf(c_5595,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | arAF0_sP0_0_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ iProver_ARSWP_104
    | ~ iProver_ARSWP_93 ),
    inference(resolution,[status(thm)],[c_2614,c_3521])).

cnf(c_5991,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_104
    | ~ iProver_ARSWP_93 ),
    inference(resolution,[status(thm)],[c_5595,c_22])).

cnf(c_6005,plain,
    ( arAF0_sP0_0_1(sK6)
    | ~ iProver_ARSWP_106
    | ~ iProver_ARSWP_104
    | ~ iProver_ARSWP_93 ),
    inference(resolution,[status(thm)],[c_5991,c_2627])).

cnf(c_6963,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ iProver_ARSWP_106
    | ~ iProver_ARSWP_104
    | ~ iProver_ARSWP_103
    | ~ iProver_ARSWP_93 ),
    inference(resolution,[status(thm)],[c_2624,c_6005])).

cnf(c_7314,plain,
    ( ~ iProver_ARSWP_106
    | ~ iProver_ARSWP_104
    | ~ iProver_ARSWP_103
    | ~ iProver_ARSWP_93
    | ~ iProver_ARSWP_91
    | arAF0_k3_xboole_0_0 = arAF0_k2_struct_0_0 ),
    inference(resolution,[status(thm)],[c_6963,c_2612])).

cnf(c_7315,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k2_struct_0_0
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7314])).

cnf(c_12957,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7917,c_4693,c_4742,c_7315])).

cnf(c_13952,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6307,c_5647,c_12957])).

cnf(c_13963,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k3_xboole_0_0)) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_13952])).

cnf(c_12300,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_11549])).

cnf(c_13423,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_12300,c_4421])).

cnf(c_13889,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_13423,c_3581])).

cnf(c_13431,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_12300,c_3581])).

cnf(c_13504,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_13431])).

cnf(c_9624,plain,
    ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(superposition,[status(thm)],[c_5352,c_3166])).

cnf(c_9677,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_9624])).

cnf(c_11776,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_9677])).

cnf(c_11805,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_11776,c_3581])).

cnf(c_11975,plain,
    ( arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_11805])).

cnf(c_12023,plain,
    ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_11975,c_4421])).

cnf(c_9676,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_9624])).

cnf(c_10428,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_9676])).

cnf(c_10686,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_10428,c_3581])).

cnf(c_10723,plain,
    ( arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_10686])).

cnf(c_10974,plain,
    ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_10723,c_4421])).

cnf(c_9622,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_5352])).

cnf(c_10463,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_9622])).

cnf(c_10134,plain,
    ( r1_tarski(sK7,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_10124])).

cnf(c_6899,plain,
    ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6706,c_3159])).

cnf(c_9911,plain,
    ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_6899])).

cnf(c_8306,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_3655])).

cnf(c_8305,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_3895])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_102
    | ~ arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_15])).

cnf(c_3150,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2623])).

cnf(c_5169,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_3150])).

cnf(c_5384,plain,
    ( r1_tarski(arAF0_sK4_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5169,c_3166])).

cnf(c_5493,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5384,c_3145])).

cnf(c_8304,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_5493])).

cnf(c_5745,plain,
    ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5493,c_3166])).

cnf(c_8303,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_5745])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(sK2(X2,X1),u1_pre_topc(X2))
    | sP0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)) != sK2(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2615,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X2)
    | ~ iProver_ARSWP_94
    | ~ arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 != arAF0_sK2_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_3156,plain,
    ( arAF0_k9_subset_1_0 != arAF0_sK2_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X2) = iProver_top
    | iProver_ARSWP_94 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2615])).

cnf(c_8301,plain,
    ( arAF0_sK2_0 != arAF0_k3_xboole_0_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X2) = iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_94 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_3156])).

cnf(c_7918,plain,
    ( r1_tarski(arAF0_k9_subset_1_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_6309])).

cnf(c_7762,plain,
    ( arAF0_sK2_0 != arAF0_k3_xboole_0_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X2) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_94 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_3156])).

cnf(c_4015,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_3655])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3380,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK6))
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_3459,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK6))
    | arAF0_k3_xboole_0_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3380])).

cnf(c_4126,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | arAF0_k3_xboole_0_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3459])).

cnf(c_4127,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | arAF0_k3_xboole_0_0 != sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_4126])).

cnf(c_4128,plain,
    ( arAF0_k3_xboole_0_0 != sK7
    | m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4127])).

cnf(c_4141,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4015,c_25,c_3661,c_4128])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_100
    | ~ arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_13])).

cnf(c_3151,plain,
    ( arAF0_k9_subset_1_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2621])).

cnf(c_6499,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4141,c_3151])).

cnf(c_7739,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4535,c_6499])).

cnf(c_7438,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | iProver_ARSWP_92 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6895,c_3145])).

cnf(c_6497,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(X0) != iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5169,c_3151])).

cnf(c_7073,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4535,c_6497])).

cnf(c_7265,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7073,c_4535])).

cnf(c_5744,plain,
    ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_5493])).

cnf(c_6345,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_5744])).

cnf(c_26,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6368,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(instantiation,[status(thm)],[c_6345])).

cnf(c_7092,plain,
    ( arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6345,c_26,c_6368])).

cnf(c_7103,plain,
    ( iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4535,c_7092])).

cnf(c_6495,plain,
    ( arAF0_k9_subset_1_0 = sK7
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_3151])).

cnf(c_6563,plain,
    ( arAF0_k9_subset_1_0 = sK7
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4535,c_6495])).

cnf(c_6494,plain,
    ( arAF0_k9_subset_1_0 = X0
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_3151])).

cnf(c_6104,plain,
    ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(arAF0_k3_xboole_0_0)) = iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_5107,c_3145])).

cnf(c_5492,plain,
    ( arAF0_sK4_0 = arAF0_k3_xboole_0_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5384,c_3159])).

cnf(c_5736,plain,
    ( arAF0_sK4_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_93 != iProver_top
    | iProver_ARSWP_91 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4535,c_5492])).

cnf(c_5168,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
    | arAF0_sP0_0_1(X2) != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_3150])).

cnf(c_3811,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_3804])).

cnf(c_4291,plain,
    ( arAF0_sP1_0_1(sK6) = iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_3811,c_4283])).

cnf(c_4148,plain,
    ( r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_91 != iProver_top ),
    inference(superposition,[status(thm)],[c_4141,c_3166])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:08:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.51/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.51/1.49  
% 7.51/1.49  ------  iProver source info
% 7.51/1.49  
% 7.51/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.51/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.51/1.49  git: non_committed_changes: false
% 7.51/1.49  git: last_make_outside_of_git: false
% 7.51/1.49  
% 7.51/1.49  ------ 
% 7.51/1.49  ------ Parsing...
% 7.51/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  ------ Proving...
% 7.51/1.49  ------ Problem Properties 
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  clauses                                 23
% 7.51/1.49  conjectures                             4
% 7.51/1.49  EPR                                     6
% 7.51/1.49  Horn                                    19
% 7.51/1.49  unary                                   4
% 7.51/1.49  binary                                  6
% 7.51/1.49  lits                                    66
% 7.51/1.49  lits eq                                 5
% 7.51/1.49  fd_pure                                 0
% 7.51/1.49  fd_pseudo                               0
% 7.51/1.49  fd_cond                                 0
% 7.51/1.49  fd_pseudo_cond                          0
% 7.51/1.49  AC symbols                              0
% 7.51/1.49  
% 7.51/1.49  ------ Input Options Time Limit: Unbounded
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing...
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.51/1.49  Current options:
% 7.51/1.49  ------ 
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing...
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing...
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing...
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  % SZS status CounterSatisfiable for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  % SZS output start Saturation for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  fof(f8,conjecture,(
% 7.51/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f9,negated_conjecture,(
% 7.51/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.51/1.49    inference(negated_conjecture,[],[f8])).
% 7.51/1.49  
% 7.51/1.49  fof(f16,plain,(
% 7.51/1.49    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 7.51/1.49    inference(ennf_transformation,[],[f9])).
% 7.51/1.49  
% 7.51/1.49  fof(f31,plain,(
% 7.51/1.49    ( ! [X0,X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f30,plain,(
% 7.51/1.49    ( ! [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) => (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_pre_topc(sK6,X0))) )),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f29,plain,(
% 7.51/1.49    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,sK5)) & l1_pre_topc(sK5))),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f32,plain,(
% 7.51/1.49    ((~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_pre_topc(sK6,sK5)) & l1_pre_topc(sK5)),
% 7.51/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f16,f31,f30,f29])).
% 7.51/1.49  
% 7.51/1.49  fof(f54,plain,(
% 7.51/1.49    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 7.51/1.49    inference(cnf_transformation,[],[f32])).
% 7.51/1.49  
% 7.51/1.49  fof(f4,axiom,(
% 7.51/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f20,plain,(
% 7.51/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.51/1.49    inference(nnf_transformation,[],[f4])).
% 7.51/1.49  
% 7.51/1.49  fof(f36,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f20])).
% 7.51/1.49  
% 7.51/1.49  fof(f1,axiom,(
% 7.51/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f11,plain,(
% 7.51/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.51/1.49    inference(ennf_transformation,[],[f1])).
% 7.51/1.49  
% 7.51/1.49  fof(f33,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f11])).
% 7.51/1.49  
% 7.51/1.49  fof(f2,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f12,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f2])).
% 7.51/1.49  
% 7.51/1.49  fof(f34,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f12])).
% 7.51/1.49  
% 7.51/1.49  fof(f37,plain,(
% 7.51/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f20])).
% 7.51/1.49  
% 7.51/1.49  fof(f17,plain,(
% 7.51/1.49    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 7.51/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.51/1.49  
% 7.51/1.49  fof(f22,plain,(
% 7.51/1.49    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.51/1.49    inference(nnf_transformation,[],[f17])).
% 7.51/1.49  
% 7.51/1.49  fof(f23,plain,(
% 7.51/1.49    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.51/1.49    inference(flattening,[],[f22])).
% 7.51/1.49  
% 7.51/1.49  fof(f24,plain,(
% 7.51/1.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.51/1.49    inference(rectify,[],[f23])).
% 7.51/1.49  
% 7.51/1.49  fof(f27,plain,(
% 7.51/1.49    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f26,plain,(
% 7.51/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f25,plain,(
% 7.51/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f28,plain,(
% 7.51/1.49    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.51/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f27,f26,f25])).
% 7.51/1.49  
% 7.51/1.49  fof(f46,plain,(
% 7.51/1.49    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f28])).
% 7.51/1.49  
% 7.51/1.49  fof(f52,plain,(
% 7.51/1.49    l1_pre_topc(sK5)),
% 7.51/1.49    inference(cnf_transformation,[],[f32])).
% 7.51/1.49  
% 7.51/1.49  fof(f5,axiom,(
% 7.51/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f14,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.51/1.49    inference(ennf_transformation,[],[f5])).
% 7.51/1.49  
% 7.51/1.49  fof(f18,plain,(
% 7.51/1.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 7.51/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.51/1.49  
% 7.51/1.49  fof(f19,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.51/1.49    inference(definition_folding,[],[f14,f18,f17])).
% 7.51/1.49  
% 7.51/1.49  fof(f50,plain,(
% 7.51/1.49    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f19])).
% 7.51/1.49  
% 7.51/1.49  fof(f21,plain,(
% 7.51/1.49    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 7.51/1.49    inference(nnf_transformation,[],[f18])).
% 7.51/1.49  
% 7.51/1.49  fof(f39,plain,(
% 7.51/1.49    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f21])).
% 7.51/1.49  
% 7.51/1.49  fof(f7,axiom,(
% 7.51/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f15,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.51/1.49    inference(ennf_transformation,[],[f7])).
% 7.51/1.49  
% 7.51/1.49  fof(f51,plain,(
% 7.51/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f15])).
% 7.51/1.49  
% 7.51/1.49  fof(f55,plain,(
% 7.51/1.49    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))),
% 7.51/1.49    inference(cnf_transformation,[],[f32])).
% 7.51/1.49  
% 7.51/1.49  fof(f53,plain,(
% 7.51/1.49    m1_pre_topc(sK6,sK5)),
% 7.51/1.49    inference(cnf_transformation,[],[f32])).
% 7.51/1.49  
% 7.51/1.49  fof(f38,plain,(
% 7.51/1.49    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f21])).
% 7.51/1.49  
% 7.51/1.49  fof(f40,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f28])).
% 7.51/1.49  
% 7.51/1.49  fof(f3,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.51/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f13,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f3])).
% 7.51/1.49  
% 7.51/1.49  fof(f35,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f13])).
% 7.51/1.49  
% 7.51/1.49  fof(f45,plain,(
% 7.51/1.49    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f28])).
% 7.51/1.49  
% 7.51/1.49  fof(f48,plain,(
% 7.51/1.49    ( ! [X0,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f28])).
% 7.51/1.49  
% 7.51/1.49  fof(f47,plain,(
% 7.51/1.49    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f28])).
% 7.51/1.49  
% 7.51/1.49  fof(f41,plain,(
% 7.51/1.49    ( ! [X0,X5,X1] : (m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f28])).
% 7.51/1.49  
% 7.51/1.49  fof(f49,plain,(
% 7.51/1.49    ( ! [X0,X3,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f28])).
% 7.51/1.49  
% 7.51/1.49  fof(f43,plain,(
% 7.51/1.49    ( ! [X0,X5,X1] : (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f28])).
% 7.51/1.49  
% 7.51/1.49  cnf(c_258,plain,( X0_2 = X0_2 ),theory(equality) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_20,negated_conjecture,
% 7.51/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 7.51/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3164,plain,
% 7.51/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3166,plain,
% 7.51/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.51/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3495,plain,
% 7.51/1.49      ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3164,c_3166]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_0,plain,
% 7.51/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2612,plain,
% 7.51/1.49      ( ~ r1_tarski(X0,X1) | ~ iProver_ARSWP_91 | arAF0_k3_xboole_0_0 = X0 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3159,plain,
% 7.51/1.49      ( arAF0_k3_xboole_0_0 = X0
% 7.51/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2612]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3661,plain,
% 7.51/1.49      ( arAF0_k3_xboole_0_0 = sK7 | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3495,c_3159]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.51/1.49      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3,plain,
% 7.51/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_159,plain,
% 7.51/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.51/1.49      inference(prop_impl,[status(thm)],[c_3]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_160,plain,
% 7.51/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.51/1.49      inference(renaming,[status(thm)],[c_159]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_204,plain,
% 7.51/1.49      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 7.51/1.49      | ~ r1_tarski(X2,X0) ),
% 7.51/1.49      inference(bin_hyper_res,[status(thm)],[c_1,c_160]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2628,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(X0))
% 7.51/1.49      | ~ r1_tarski(X1,X0)
% 7.51/1.49      | ~ iProver_ARSWP_107 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_204]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3145,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(X0)) = iProver_top
% 7.51/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2628]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3655,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3495,c_3145]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3895,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(sK6)) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3655,c_3166]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4001,plain,
% 7.51/1.49      ( arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3895,c_3159]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_10,plain,
% 7.51/1.49      ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 7.51/1.49      | sP0(X0,X1)
% 7.51/1.49      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.49      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2618,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
% 7.51/1.49      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.49      | arAF0_sP0_0_1(X1)
% 7.51/1.49      | ~ iProver_ARSWP_97
% 7.51/1.49      | arAF0_r2_hidden_0 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3153,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2618]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6706,plain,
% 7.51/1.49      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3153,c_3166]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6901,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_6706,c_3145]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11490,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_6901,c_3166]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11550,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4001,c_11490]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14147,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3661,c_11550]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_22,negated_conjecture,
% 7.51/1.49      ( l1_pre_topc(sK5) ),
% 7.51/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3163,plain,
% 7.51/1.49      ( l1_pre_topc(sK5) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_17,plain,
% 7.51/1.49      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2625,plain,
% 7.51/1.49      ( arAF0_sP1_0_1(X0)
% 7.51/1.49      | ~ l1_pre_topc(X1)
% 7.51/1.49      | ~ l1_pre_topc(X0)
% 7.51/1.49      | ~ iProver_ARSWP_104 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_17]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3148,plain,
% 7.51/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.51/1.49      | l1_pre_topc(X1) != iProver_top
% 7.51/1.49      | l1_pre_topc(X0) != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2625]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3521,plain,
% 7.51/1.49      ( arAF0_sP1_0_1(X0) | ~ l1_pre_topc(X0) | ~ iProver_ARSWP_104 ),
% 7.51/1.49      inference(resolution,[status(thm)],[c_2625,c_22]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3522,plain,
% 7.51/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.51/1.49      | l1_pre_topc(X0) != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3521]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4283,plain,
% 7.51/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.51/1.49      | l1_pre_topc(X0) != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top ),
% 7.51/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3148,c_3522]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4290,plain,
% 7.51/1.49      ( arAF0_sP1_0_1(sK5) = iProver_top | iProver_ARSWP_104 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3163,c_4283]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_5,plain,
% 7.51/1.49      ( ~ sP1(X0,X1) | ~ sP0(X1,X0) | m1_pre_topc(X1,X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2613,plain,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(X0)
% 7.51/1.49      | ~ arAF0_sP0_0_1(X0)
% 7.51/1.49      | ~ arAF0_sP1_0_1(X1)
% 7.51/1.49      | ~ iProver_ARSWP_92 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3158,plain,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X0) != iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X1) != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2613]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4421,plain,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X0) != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4290,c_3158]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14429,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_14147,c_4421]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_18,plain,
% 7.51/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2626,plain,
% 7.51/1.49      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 7.51/1.49      | ~ l1_pre_topc(X1)
% 7.51/1.49      | l1_pre_topc(X0)
% 7.51/1.49      | ~ iProver_ARSWP_105 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_18]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3147,plain,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.51/1.49      | l1_pre_topc(X1) != iProver_top
% 7.51/1.49      | l1_pre_topc(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2626]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3605,plain,
% 7.51/1.49      ( ~ arAF0_m1_pre_topc_0_1(X0) | l1_pre_topc(X0) | ~ iProver_ARSWP_105 ),
% 7.51/1.49      inference(resolution,[status(thm)],[c_2626,c_22]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3606,plain,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.51/1.49      | l1_pre_topc(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3605]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3804,plain,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.51/1.49      | l1_pre_topc(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.51/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3147,c_3606]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14841,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | l1_pre_topc(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_14429,c_3804]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_17508,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_14841,c_4283]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3167,plain,
% 7.51/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.51/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_19,negated_conjecture,
% 7.51/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.51/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3165,plain,
% 7.51/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3581,plain,
% 7.51/1.49      ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3167,c_3165]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_18819,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_17508,c_3581]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_21,negated_conjecture,
% 7.51/1.49      ( m1_pre_topc(sK6,sK5) ),
% 7.51/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2627,negated_conjecture,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(sK6) | ~ iProver_ARSWP_106 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_21]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3146,plain,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(sK6) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2627]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6,plain,
% 7.51/1.49      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2614,plain,
% 7.51/1.49      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 7.51/1.49      | arAF0_sP0_0_1(X0)
% 7.51/1.49      | ~ arAF0_sP1_0_1(X1)
% 7.51/1.49      | ~ iProver_ARSWP_93 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3157,plain,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X1) != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2614]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4412,plain,
% 7.51/1.49      ( arAF0_sP0_0_1(sK6) = iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X0) != iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3146,c_3157]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4535,plain,
% 7.51/1.49      ( arAF0_sP0_0_1(sK6) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4290,c_4412]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_16,plain,
% 7.51/1.49      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2624,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.49      | ~ arAF0_sP0_0_1(X0)
% 7.51/1.49      | ~ iProver_ARSWP_103 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_16]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3149,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X0) != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2624]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4742,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4535,c_3149]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14437,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_14147,c_3581]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14571,plain,
% 7.51/1.49      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4742,c_14437]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14792,plain,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_14571,c_4421]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_15061,plain,
% 7.51/1.49      ( l1_pre_topc(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_14792,c_3804]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_18105,plain,
% 7.51/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_15061,c_4283]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2,plain,
% 7.51/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.51/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_205,plain,
% 7.51/1.49      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.51/1.49      inference(bin_hyper_res,[status(thm)],[c_2,c_160]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2629,plain,
% 7.51/1.49      ( ~ r1_tarski(X0,X1)
% 7.51/1.49      | ~ iProver_ARSWP_108
% 7.51/1.49      | arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_205]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3144,plain,
% 7.51/1.49      ( arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.51/1.49      | iProver_ARSWP_108 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2629]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8214,plain,
% 7.51/1.49      ( arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | iProver_ARSWP_108 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3495,c_3144]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11481,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_108 != iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_8214,c_6901]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_12530,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_108 != iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_11481,c_4421]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_13718,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | l1_pre_topc(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_108 != iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_12530,c_3804]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_17928,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_108 != iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_13718,c_4283]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_17511,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | l1_pre_topc(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_14841,c_3581]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6895,plain,
% 7.51/1.49      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_6706,c_4421]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_7435,plain,
% 7.51/1.49      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | l1_pre_topc(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_6895,c_3804]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_15219,plain,
% 7.51/1.49      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_7435,c_4283]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_17146,plain,
% 7.51/1.49      ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_15219,c_3159]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_17221,plain,
% 7.51/1.49      ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4742,c_17146]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_17148,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_15219,c_3145]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11549,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_108 != iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_8214,c_11490]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_12302,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_108 != iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_11549,c_4421]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_13588,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | l1_pre_topc(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_108 != iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_12302,c_3804]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_16934,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_108 != iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_13588,c_4283]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11,plain,
% 7.51/1.49      ( sP0(X0,X1)
% 7.51/1.49      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.51/1.49      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2619,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0)))
% 7.51/1.49      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.49      | arAF0_sP0_0_1(X0)
% 7.51/1.49      | ~ iProver_ARSWP_98 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3152,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_98 != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2619]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4526,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | r1_tarski(arAF0_sK2_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_98 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3152,c_3166]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_5351,plain,
% 7.51/1.49      ( arAF0_sK2_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_98 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4526,c_3159]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_9864,plain,
% 7.51/1.49      ( arAF0_sK2_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_98 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4742,c_5351]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_15756,plain,
% 7.51/1.49      ( arAF0_sK2_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_98 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_9864,c_4421]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_15855,plain,
% 7.51/1.49      ( arAF0_sK2_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | l1_pre_topc(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_98 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_15756,c_3804]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_16918,plain,
% 7.51/1.49      ( arAF0_sK2_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_98 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_15855,c_4283]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8,plain,
% 7.51/1.49      ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 7.51/1.49      | sP0(X0,X1)
% 7.51/1.49      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
% 7.51/1.49      | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2616,plain,
% 7.51/1.49      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.49      | arAF0_sP0_0_1(X0)
% 7.51/1.49      | ~ iProver_ARSWP_95
% 7.51/1.49      | arAF0_r2_hidden_0
% 7.51/1.49      | arAF0_k9_subset_1_0 = arAF0_sK2_0 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3155,plain,
% 7.51/1.49      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_95 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2616]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_5524,plain,
% 7.51/1.49      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.51/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_95 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4742,c_3155]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14104,plain,
% 7.51/1.49      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.51/1.49      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_95 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_5524,c_4421]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14647,plain,
% 7.51/1.49      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.51/1.49      | l1_pre_topc(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_95 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_14104,c_3804]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_16797,plain,
% 7.51/1.49      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.51/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_95 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_14647,c_4283]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11552,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_11490,c_4421]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_13349,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | l1_pre_topc(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_11552,c_3804]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_16592,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_97 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_13349,c_4283]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_9,plain,
% 7.51/1.49      ( r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
% 7.51/1.49      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 7.51/1.49      | sP0(X0,X1)
% 7.51/1.49      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2617,plain,
% 7.51/1.49      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.49      | arAF0_sP0_0_1(X0)
% 7.51/1.49      | ~ iProver_ARSWP_96
% 7.51/1.49      | arAF0_r2_hidden_0 ),
% 7.51/1.49      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3154,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_96 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2617]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4866,plain,
% 7.51/1.49      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_96 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4742,c_3154]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11320,plain,
% 7.51/1.49      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_96 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4866,c_4421]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_12491,plain,
% 7.51/1.49      ( l1_pre_topc(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_96 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_11320,c_3804]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_16575,plain,
% 7.51/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_105 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_96 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_92 != iProver_top
% 7.51/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_12491,c_4283]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4865,plain,
% 7.51/1.49      ( arAF0_k2_struct_0_0 = arAF0_k3_xboole_0_0
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4742,c_3159]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_5107,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4865,c_4742]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6101,plain,
% 7.51/1.49      ( r1_tarski(sK7,sK7) = iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3661,c_5107]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6141,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_6101,c_3145]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_12793,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4001,c_6141]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6640,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(sK7))
% 7.51/1.49      | ~ r1_tarski(arAF0_k3_xboole_0_0,sK7) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6641,plain,
% 7.51/1.49      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.51/1.49      | r1_tarski(arAF0_k3_xboole_0_0,sK7) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_6640]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_12794,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k9_subset_1_0,sK7) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_6141,c_3166]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_12938,plain,
% 7.51/1.49      ( r1_tarski(arAF0_k3_xboole_0_0,sK7) = iProver_top
% 7.51/1.49      | iProver_ARSWP_107 != iProver_top
% 7.51/1.49      | iProver_ARSWP_106 != iProver_top
% 7.51/1.49      | iProver_ARSWP_104 != iProver_top
% 7.51/1.49      | iProver_ARSWP_103 != iProver_top
% 7.51/1.49      | iProver_ARSWP_93 != iProver_top
% 7.51/1.49      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_4001,c_12794]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3403,plain,
% 7.51/1.49      ( r1_tarski(sK7,u1_struct_0(sK6)) ),
% 7.51/1.49      inference(resolution,[status(thm)],[c_4,c_20]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4545,plain,
% 7.51/1.49      ( ~ iProver_ARSWP_91 | arAF0_k3_xboole_0_0 = sK7 ),
% 7.51/1.49      inference(resolution,[status(thm)],[c_2612,c_3403]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_272,plain,
% 7.51/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.51/1.50      theory(equality) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4578,plain,
% 7.51/1.50      ( r1_tarski(X0,arAF0_k3_xboole_0_0)
% 7.51/1.50      | ~ r1_tarski(X1,sK7)
% 7.51/1.50      | ~ iProver_ARSWP_91
% 7.51/1.50      | X0 != X1 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_4545,c_272]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_271,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_270,plain,( X0 = X0 ),theory(equality) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3747,plain,
% 7.51/1.50      ( X0 != X1 | X1 = X0 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_271,c_270]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4555,plain,
% 7.51/1.50      ( ~ iProver_ARSWP_91 | sK7 = arAF0_k3_xboole_0_0 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_4545,c_3747]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6202,plain,
% 7.51/1.50      ( ~ r1_tarski(arAF0_k3_xboole_0_0,sK7)
% 7.51/1.50      | r1_tarski(sK7,arAF0_k3_xboole_0_0)
% 7.51/1.50      | ~ iProver_ARSWP_91 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_4578,c_4555]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4345,plain,
% 7.51/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_272,c_270]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5794,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,X0)
% 7.51/1.50      | ~ r1_tarski(sK7,X0)
% 7.51/1.50      | ~ iProver_ARSWP_91 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_4345,c_4545]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6573,plain,
% 7.51/1.50      ( r1_tarski(sK7,arAF0_k3_xboole_0_0)
% 7.51/1.50      | ~ r1_tarski(sK7,sK7)
% 7.51/1.50      | ~ iProver_ARSWP_91 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_6202,c_5794]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6574,plain,
% 7.51/1.50      ( r1_tarski(sK7,arAF0_k3_xboole_0_0) = iProver_top
% 7.51/1.50      | r1_tarski(sK7,sK7) != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_6573]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4615,plain,
% 7.51/1.50      ( ~ r1_tarski(X0,arAF0_k3_xboole_0_0)
% 7.51/1.50      | r1_tarski(X1,sK7)
% 7.51/1.50      | ~ iProver_ARSWP_91
% 7.51/1.50      | X1 != X0 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_4555,c_272]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_12609,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,sK7)
% 7.51/1.50      | ~ r1_tarski(sK7,arAF0_k3_xboole_0_0)
% 7.51/1.50      | ~ iProver_ARSWP_91 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_4615,c_4545]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_12610,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,sK7) = iProver_top
% 7.51/1.50      | r1_tarski(sK7,arAF0_k3_xboole_0_0) != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_12609]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_13172,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,sK7) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_12938,c_6101,c_6574,c_12610]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_16431,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_12793,c_6101,c_6574,c_6641,c_12610]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5352,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4526,c_3145]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_9623,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4001,c_5352]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_16258,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3661,c_9623]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6702,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3153,c_4421]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7512,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | l1_pre_topc(X1) = iProver_top
% 7.51/1.50      | iProver_ARSWP_105 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_6702,c_3804]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_16228,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP1_0_1(X1) = iProver_top
% 7.51/1.50      | iProver_ARSWP_105 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_7512,c_4283]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4867,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4742,c_3145]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8302,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_8214,c_4867]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_9412,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3661,c_8302]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5882,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.51/1.50      | ~ r1_tarski(sK7,arAF0_k2_struct_0_0) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5883,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.51/1.50      | r1_tarski(sK7,arAF0_k2_struct_0_0) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_5882]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6309,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k9_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4867,c_3166]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8300,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_8214,c_6309]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_9172,plain,
% 7.51/1.50      ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3661,c_8300]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_25,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2520,plain,
% 7.51/1.50      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.51/1.50      | r1_tarski(sK7,u1_struct_0(sK6)) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2521,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.51/1.50      | r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_2520]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3450,plain,
% 7.51/1.50      ( ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.51/1.50      | ~ iProver_ARSWP_91
% 7.51/1.50      | arAF0_k3_xboole_0_0 = sK7 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_2612]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3451,plain,
% 7.51/1.50      ( arAF0_k3_xboole_0_0 = sK7
% 7.51/1.50      | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_3450]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4556,plain,
% 7.51/1.50      ( sK7 = arAF0_k3_xboole_0_0 | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_4555]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8197,plain,
% 7.51/1.50      ( r1_tarski(X0,X1)
% 7.51/1.50      | ~ r1_tarski(sK7,arAF0_k3_xboole_0_0)
% 7.51/1.50      | X1 != arAF0_k3_xboole_0_0
% 7.51/1.50      | X0 != sK7 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_272]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8626,plain,
% 7.51/1.50      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.51/1.50      | ~ r1_tarski(sK7,arAF0_k3_xboole_0_0)
% 7.51/1.50      | X0 != sK7
% 7.51/1.50      | arAF0_k2_struct_0_0 != arAF0_k3_xboole_0_0 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_8197]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8829,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | ~ r1_tarski(sK7,arAF0_k3_xboole_0_0)
% 7.51/1.50      | arAF0_k2_struct_0_0 != arAF0_k3_xboole_0_0
% 7.51/1.50      | arAF0_k3_xboole_0_0 != sK7 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_8626]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8830,plain,
% 7.51/1.50      ( arAF0_k2_struct_0_0 != arAF0_k3_xboole_0_0
% 7.51/1.50      | arAF0_k3_xboole_0_0 != sK7
% 7.51/1.50      | r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.51/1.50      | r1_tarski(sK7,arAF0_k3_xboole_0_0) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_8829]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5645,plain,
% 7.51/1.50      ( r1_tarski(X0,X1)
% 7.51/1.50      | ~ r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | X1 != arAF0_k2_struct_0_0
% 7.51/1.50      | X0 != arAF0_k3_xboole_0_0 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_272]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7244,plain,
% 7.51/1.50      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.51/1.50      | ~ r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | X0 != arAF0_k3_xboole_0_0
% 7.51/1.50      | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_5645]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7245,plain,
% 7.51/1.50      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.51/1.50      | ~ r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | X0 != arAF0_k3_xboole_0_0 ),
% 7.51/1.50      inference(equality_resolution_simp,[status(thm)],[c_7244]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_9559,plain,
% 7.51/1.50      ( ~ r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | r1_tarski(sK7,arAF0_k2_struct_0_0)
% 7.51/1.50      | sK7 != arAF0_k3_xboole_0_0 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_7245]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_9560,plain,
% 7.51/1.50      ( sK7 != arAF0_k3_xboole_0_0
% 7.51/1.50      | r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_9559]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10124,plain,
% 7.51/1.50      ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_9172,c_25,c_2521,c_3451,c_4556,c_4865,c_6101,c_6574,
% 7.51/1.50                 c_8830,c_9560]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10151,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_9412,c_25,c_2521,c_3451,c_4556,c_4865,c_5883,c_6101,
% 7.51/1.50                 c_6574,c_8830,c_9560]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10161,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k3_xboole_0_0)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4865,c_10151]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15469,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3661,c_10161]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15220,plain,
% 7.51/1.50      ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | l1_pre_topc(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_105 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_7435,c_3159]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15291,plain,
% 7.51/1.50      ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
% 7.51/1.50      | l1_pre_topc(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_105 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4742,c_15220]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15222,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | l1_pre_topc(X1) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_105 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_7435,c_3145]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_14844,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_14429,c_3581]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7436,plain,
% 7.51/1.50      ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_6895,c_3159]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_14281,plain,
% 7.51/1.50      ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
% 7.51/1.50      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4742,c_7436]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6307,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4001,c_4867]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5646,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.51/1.50      | ~ r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5647,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_5646]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7917,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4001,c_6309]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3699,plain,
% 7.51/1.50      ( r1_tarski(X0,X1)
% 7.51/1.50      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | X0 != arAF0_k2_struct_0_0
% 7.51/1.50      | X1 != arAF0_k2_struct_0_0 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_272]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4250,plain,
% 7.51/1.50      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.51/1.50      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | X0 != arAF0_k2_struct_0_0
% 7.51/1.50      | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_3699]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4251,plain,
% 7.51/1.50      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.51/1.50      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | X0 != arAF0_k2_struct_0_0 ),
% 7.51/1.50      inference(equality_resolution_simp,[status(thm)],[c_4250]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4692,plain,
% 7.51/1.50      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | arAF0_k3_xboole_0_0 != arAF0_k2_struct_0_0 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_4251]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4693,plain,
% 7.51/1.50      ( arAF0_k3_xboole_0_0 != arAF0_k2_struct_0_0
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_4692]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5595,plain,
% 7.51/1.50      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 7.51/1.50      | arAF0_sP0_0_1(X0)
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | ~ iProver_ARSWP_104
% 7.51/1.50      | ~ iProver_ARSWP_93 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_2614,c_3521]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5991,plain,
% 7.51/1.50      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 7.51/1.50      | arAF0_sP0_0_1(X0)
% 7.51/1.50      | ~ iProver_ARSWP_104
% 7.51/1.50      | ~ iProver_ARSWP_93 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_5595,c_22]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6005,plain,
% 7.51/1.50      ( arAF0_sP0_0_1(sK6)
% 7.51/1.50      | ~ iProver_ARSWP_106
% 7.51/1.50      | ~ iProver_ARSWP_104
% 7.51/1.50      | ~ iProver_ARSWP_93 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_5991,c_2627]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6963,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | ~ iProver_ARSWP_106
% 7.51/1.50      | ~ iProver_ARSWP_104
% 7.51/1.50      | ~ iProver_ARSWP_103
% 7.51/1.50      | ~ iProver_ARSWP_93 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_2624,c_6005]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7314,plain,
% 7.51/1.50      ( ~ iProver_ARSWP_106
% 7.51/1.50      | ~ iProver_ARSWP_104
% 7.51/1.50      | ~ iProver_ARSWP_103
% 7.51/1.50      | ~ iProver_ARSWP_93
% 7.51/1.50      | ~ iProver_ARSWP_91
% 7.51/1.50      | arAF0_k3_xboole_0_0 = arAF0_k2_struct_0_0 ),
% 7.51/1.50      inference(resolution,[status(thm)],[c_6963,c_2612]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7315,plain,
% 7.51/1.50      ( arAF0_k3_xboole_0_0 = arAF0_k2_struct_0_0
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_7314]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_12957,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_7917,c_4693,c_4742,c_7315]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_13952,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_6307,c_5647,c_12957]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_13963,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(arAF0_k3_xboole_0_0)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4865,c_13952]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_12300,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X1) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3661,c_11549]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_13423,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.51/1.50      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_12300,c_4421]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_13889,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_13423,c_3581]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_13431,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_12300,c_3581]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_13504,plain,
% 7.51/1.50      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4742,c_13431]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_9624,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_5352,c_3166]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_9677,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4001,c_9624]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_11776,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3661,c_9677]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_11805,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK5) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_11776,c_3581]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_11975,plain,
% 7.51/1.50      ( arAF0_sP0_0_1(sK5) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4742,c_11805]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_12023,plain,
% 7.51/1.50      ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_11975,c_4421]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_9676,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_8214,c_9624]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10428,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3661,c_9676]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10686,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK5) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_10428,c_3581]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10723,plain,
% 7.51/1.50      ( arAF0_sP0_0_1(sK5) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4742,c_10686]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10974,plain,
% 7.51/1.50      ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_10723,c_4421]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_9622,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_8214,c_5352]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10463,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_98 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3661,c_9622]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10134,plain,
% 7.51/1.50      ( r1_tarski(sK7,arAF0_k3_xboole_0_0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4865,c_10124]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6899,plain,
% 7.51/1.50      ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_6706,c_3159]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_9911,plain,
% 7.51/1.50      ( arAF0_sK3_0 = arAF0_k3_xboole_0_0
% 7.51/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4742,c_6899]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8306,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_8214,c_3655]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8305,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(sK6)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_8214,c_3895]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15,plain,
% 7.51/1.50      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.51/1.50      | ~ sP0(X1,X2)
% 7.51/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) ),
% 7.51/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2623,plain,
% 7.51/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.51/1.50      | ~ arAF0_sP0_0_1(X1)
% 7.51/1.50      | ~ iProver_ARSWP_102
% 7.51/1.50      | ~ arAF0_r2_hidden_0 ),
% 7.51/1.50      inference(arg_filter_abstr,[status(unp)],[c_15]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3150,plain,
% 7.51/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.51/1.50      | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X1) != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_2623]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5169,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3164,c_3150]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5384,plain,
% 7.51/1.50      ( r1_tarski(arAF0_sK4_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_5169,c_3166]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5493,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_5384,c_3145]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8304,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_8214,c_5493]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5745,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k9_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_5493,c_3166]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8303,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_8214,c_5745]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7,plain,
% 7.51/1.50      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.51/1.50      | ~ r2_hidden(sK2(X2,X1),u1_pre_topc(X2))
% 7.51/1.50      | sP0(X2,X1)
% 7.51/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
% 7.51/1.50      | k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)) != sK2(X2,X1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2615,plain,
% 7.51/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.51/1.50      | arAF0_sP0_0_1(X2)
% 7.51/1.50      | ~ iProver_ARSWP_94
% 7.51/1.50      | ~ arAF0_r2_hidden_0
% 7.51/1.50      | arAF0_k9_subset_1_0 != arAF0_sK2_0 ),
% 7.51/1.50      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3156,plain,
% 7.51/1.50      ( arAF0_k9_subset_1_0 != arAF0_sK2_0
% 7.51/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X2) = iProver_top
% 7.51/1.50      | iProver_ARSWP_94 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_2615]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8301,plain,
% 7.51/1.50      ( arAF0_sK2_0 != arAF0_k3_xboole_0_0
% 7.51/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X2) = iProver_top
% 7.51/1.50      | iProver_ARSWP_108 != iProver_top
% 7.51/1.50      | iProver_ARSWP_94 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_8214,c_3156]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7918,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k9_subset_1_0,arAF0_k3_xboole_0_0) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4865,c_6309]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7762,plain,
% 7.51/1.50      ( arAF0_sK2_0 != arAF0_k3_xboole_0_0
% 7.51/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X2) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_94 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4001,c_3156]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4015,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4001,c_3655]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_275,plain,
% 7.51/1.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.51/1.50      theory(equality) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3380,plain,
% 7.51/1.50      ( m1_subset_1(X0,X1)
% 7.51/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.51/1.50      | X1 != k1_zfmisc_1(u1_struct_0(sK6))
% 7.51/1.50      | X0 != sK7 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_275]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3459,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,X0)
% 7.51/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.51/1.50      | X0 != k1_zfmisc_1(u1_struct_0(sK6))
% 7.51/1.50      | arAF0_k3_xboole_0_0 != sK7 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_3380]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4126,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.51/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.51/1.50      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 7.51/1.50      | arAF0_k3_xboole_0_0 != sK7 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_3459]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4127,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.51/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.51/1.50      | arAF0_k3_xboole_0_0 != sK7 ),
% 7.51/1.50      inference(equality_resolution_simp,[status(thm)],[c_4126]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4128,plain,
% 7.51/1.50      ( arAF0_k3_xboole_0_0 != sK7
% 7.51/1.50      | m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.51/1.50      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_4127]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4141,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_4015,c_25,c_3661,c_4128]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_13,plain,
% 7.51/1.50      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.51/1.50      | ~ sP0(X1,X2)
% 7.51/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
% 7.51/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2621,plain,
% 7.51/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | ~ arAF0_sP0_0_1(X1)
% 7.51/1.50      | ~ iProver_ARSWP_100
% 7.51/1.50      | ~ arAF0_r2_hidden_0
% 7.51/1.50      | arAF0_k9_subset_1_0 = X0 ),
% 7.51/1.50      inference(arg_filter_abstr,[status(unp)],[c_13]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3151,plain,
% 7.51/1.50      ( arAF0_k9_subset_1_0 = X0
% 7.51/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X1) != iProver_top
% 7.51/1.50      | iProver_ARSWP_100 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_2621]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6499,plain,
% 7.51/1.50      ( arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_100 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4141,c_3151]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7739,plain,
% 7.51/1.50      ( arAF0_k9_subset_1_0 = arAF0_k3_xboole_0_0
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_100 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4535,c_6499]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7438,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.51/1.50      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_97 != iProver_top
% 7.51/1.50      | iProver_ARSWP_92 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_6895,c_3145]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6497,plain,
% 7.51/1.50      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 7.51/1.50      | arAF0_sP0_0_1(X0) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | iProver_ARSWP_100 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_5169,c_3151]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7073,plain,
% 7.51/1.50      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | iProver_ARSWP_100 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4535,c_6497]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7265,plain,
% 7.51/1.50      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | iProver_ARSWP_100 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(global_propositional_subsumption,[status(thm)],[c_7073,c_4535]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5744,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k3_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4001,c_5493]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6345,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3661,c_5744]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_26,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6368,plain,
% 7.51/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_6345]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7092,plain,
% 7.51/1.50      ( arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_6345,c_26,c_6368]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7103,plain,
% 7.51/1.50      ( iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4535,c_7092]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6495,plain,
% 7.51/1.50      ( arAF0_k9_subset_1_0 = sK7
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_100 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3164,c_3151]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6563,plain,
% 7.51/1.50      ( arAF0_k9_subset_1_0 = sK7
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_100 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4535,c_6495]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6494,plain,
% 7.51/1.50      ( arAF0_k9_subset_1_0 = X0
% 7.51/1.50      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X1) != iProver_top
% 7.51/1.50      | iProver_ARSWP_100 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3167,c_3151]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6104,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_k9_subset_1_0,k1_zfmisc_1(arAF0_k3_xboole_0_0)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_107 != iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_103 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_5107,c_3145]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5492,plain,
% 7.51/1.50      ( arAF0_sK4_0 = arAF0_k3_xboole_0_0
% 7.51/1.50      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_5384,c_3159]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5736,plain,
% 7.51/1.50      ( arAF0_sK4_0 = arAF0_k3_xboole_0_0
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | iProver_ARSWP_93 != iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4535,c_5492]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5168,plain,
% 7.51/1.50      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.51/1.50      | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
% 7.51/1.50      | arAF0_sP0_0_1(X2) != iProver_top
% 7.51/1.50      | iProver_ARSWP_102 != iProver_top
% 7.51/1.50      | arAF0_r2_hidden_0 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3167,c_3150]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3811,plain,
% 7.51/1.50      ( l1_pre_topc(sK6) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_105 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3146,c_3804]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4291,plain,
% 7.51/1.50      ( arAF0_sP1_0_1(sK6) = iProver_top
% 7.51/1.50      | iProver_ARSWP_106 != iProver_top
% 7.51/1.50      | iProver_ARSWP_105 != iProver_top
% 7.51/1.50      | iProver_ARSWP_104 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_3811,c_4283]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4148,plain,
% 7.51/1.50      ( r1_tarski(arAF0_k3_xboole_0_0,u1_struct_0(sK6)) = iProver_top
% 7.51/1.50      | iProver_ARSWP_91 != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4141,c_3166]) ).
% 7.51/1.50  
% 7.51/1.50  
% 7.51/1.50  % SZS output end Saturation for theBenchmark.p
% 7.51/1.50  
% 7.51/1.50  ------                               Statistics
% 7.51/1.50  
% 7.51/1.50  ------ Selected
% 7.51/1.50  
% 7.51/1.50  total_time:                             0.519
% 7.51/1.50  
%------------------------------------------------------------------------------
