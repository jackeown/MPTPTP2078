%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:28 EST 2020

% Result     : CounterSatisfiable 7.90s
% Output     : Saturation 7.90s
% Verified   : 
% Statistics : Number of formulae       :  437 (18088 expanded)
%              Number of clauses        :  383 (7157 expanded)
%              Number of leaves         :   20 (4985 expanded)
%              Depth                    :   19
%              Number of atoms          : 2332 (81878 expanded)
%              Number of equality atoms : 1866 (17145 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_pre_topc(sK6,sK5)
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f18,f33,f32,f31])).

fof(f57,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
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

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f29,f28,f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f20,f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1)
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_272,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3321,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3323,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3660,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_3323])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_167,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_168,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_167])).

cnf(c_215,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_168])).

cnf(c_2743,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ iProver_ARSWP_115
    | arAF0_k3_subset_1_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_215])).

cnf(c_3300,plain,
    ( arAF0_k3_subset_1_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | iProver_ARSWP_115 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2743])).

cnf(c_4172,plain,
    ( arAF0_k3_subset_1_0 = sK7
    | iProver_ARSWP_115 != iProver_top ),
    inference(superposition,[status(thm)],[c_3660,c_3300])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2725,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(arAF0_k4_xboole_0_0,X1)
    | ~ iProver_ARSWP_97 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_3316,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,X1) = iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2725])).

cnf(c_3904,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_3660,c_3316])).

cnf(c_4173,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_3904,c_3300])).

cnf(c_4288,plain,
    ( arAF0_k4_xboole_0_0 = sK7
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_4173])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2731,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_103
    | arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_3310,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_103 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2731])).

cnf(c_6882,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_103 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3310,c_3323])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3320,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2738,plain,
    ( arAF0_sP1_0_1(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ iProver_ARSWP_110 ),
    inference(arg_filter_abstr,[status(unp)],[c_18])).

cnf(c_3305,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_110 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2738])).

cnf(c_3686,plain,
    ( arAF0_sP1_0_1(X0)
    | ~ l1_pre_topc(X0)
    | ~ iProver_ARSWP_110 ),
    inference(resolution,[status(thm)],[c_2738,c_23])).

cnf(c_3687,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_110 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3686])).

cnf(c_4434,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_110 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3305,c_3687])).

cnf(c_4441,plain,
    ( arAF0_sP1_0_1(sK5) = iProver_top
    | iProver_ARSWP_110 != iProver_top ),
    inference(superposition,[status(thm)],[c_3320,c_4434])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2726,plain,
    ( arAF0_m1_pre_topc_0_1(X0)
    | ~ arAF0_sP0_0_1(X0)
    | ~ arAF0_sP1_0_1(X1)
    | ~ iProver_ARSWP_98 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_3315,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | arAF0_sP1_0_1(X1) != iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2726])).

cnf(c_4672,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(superposition,[status(thm)],[c_4441,c_3315])).

cnf(c_6921,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6882,c_4672])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2739,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_111 ),
    inference(arg_filter_abstr,[status(unp)],[c_19])).

cnf(c_3304,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_111 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2739])).

cnf(c_3770,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_111 ),
    inference(resolution,[status(thm)],[c_2739,c_23])).

cnf(c_3771,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_111 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3770])).

cnf(c_3971,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_111 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3304,c_3771])).

cnf(c_7749,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6921,c_3971])).

cnf(c_17078,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7749,c_3316])).

cnf(c_18056,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_17078])).

cnf(c_23128,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_18056,c_4434])).

cnf(c_3324,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3322,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3746,plain,
    ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3324,c_3322])).

cnf(c_27575,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_23128,c_3746])).

cnf(c_17076,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7749,c_4434])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_214,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_168])).

cnf(c_2742,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ iProver_ARSWP_114 ),
    inference(arg_filter_abstr,[status(unp)],[c_214])).

cnf(c_3301,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2742])).

cnf(c_21167,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17076,c_3301])).

cnf(c_25964,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_21167])).

cnf(c_26305,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_25964,c_3322])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2740,negated_conjecture,
    ( arAF0_m1_pre_topc_0_1(sK6)
    | ~ iProver_ARSWP_112 ),
    inference(arg_filter_abstr,[status(unp)],[c_22])).

cnf(c_3303,plain,
    ( arAF0_m1_pre_topc_0_1(sK6) = iProver_top
    | iProver_ARSWP_112 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2740])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2727,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | arAF0_sP0_0_1(X0)
    | ~ arAF0_sP1_0_1(X1)
    | ~ iProver_ARSWP_99 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_3314,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | arAF0_sP1_0_1(X1) != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2727])).

cnf(c_4567,plain,
    ( arAF0_sP0_0_1(sK6) = iProver_top
    | arAF0_sP1_0_1(X0) != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_3303,c_3314])).

cnf(c_4783,plain,
    ( arAF0_sP0_0_1(sK6) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_4441,c_4567])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2737,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_109 ),
    inference(arg_filter_abstr,[status(unp)],[c_17])).

cnf(c_3306,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | iProver_ARSWP_109 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2737])).

cnf(c_4953,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_3306])).

cnf(c_5089,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k2_struct_0_0
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_3300])).

cnf(c_6401,plain,
    ( arAF0_k2_struct_0_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_4173])).

cnf(c_5091,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_3301])).

cnf(c_15957,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_5091])).

cnf(c_13263,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
    | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_13264,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13263])).

cnf(c_9716,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5091,c_3323])).

cnf(c_15956,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_9716])).

cnf(c_286,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4055,plain,
    ( X0 != X1
    | X0 = arAF0_k3_subset_1_0
    | arAF0_k3_subset_1_0 != X1 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_4728,plain,
    ( X0 = arAF0_k3_subset_1_0
    | X0 != arAF0_k4_xboole_0_0
    | arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0 ),
    inference(instantiation,[status(thm)],[c_4055])).

cnf(c_5872,plain,
    ( arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0
    | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
    | arAF0_k4_xboole_0_0 != arAF0_k4_xboole_0_0 ),
    inference(instantiation,[status(thm)],[c_4728])).

cnf(c_5873,plain,
    ( arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0
    | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5872])).

cnf(c_287,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3873,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k2_struct_0_0
    | X1 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_4937,plain,
    ( r1_tarski(X0,arAF0_k3_subset_1_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k2_struct_0_0
    | arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_3873])).

cnf(c_6333,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_4937])).

cnf(c_6334,plain,
    ( arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6333])).

cnf(c_5726,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
    | X0 != arAF0_k3_subset_1_0
    | X1 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_7675,plain,
    ( r1_tarski(X0,arAF0_k4_xboole_0_0)
    | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
    | X0 != arAF0_k3_subset_1_0
    | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_5726])).

cnf(c_10263,plain,
    ( ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0)
    | arAF0_k3_subset_1_0 != arAF0_k3_subset_1_0
    | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_7675])).

cnf(c_10264,plain,
    ( ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0)
    | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_10263])).

cnf(c_10265,plain,
    ( arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0) != iProver_top
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10264])).

cnf(c_17296,plain,
    ( iProver_ARSWP_115 != iProver_top
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15956,c_4173,c_4953,c_5089,c_5873,c_6334,c_10265])).

cnf(c_17297,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(renaming,[status(thm)],[c_17296])).

cnf(c_25744,plain,
    ( iProver_ARSWP_115 != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15957,c_13264,c_17297])).

cnf(c_25745,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(renaming,[status(thm)],[c_25744])).

cnf(c_25756,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_25745])).

cnf(c_6927,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6882,c_3316])).

cnf(c_13629,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_6927])).

cnf(c_19253,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_13629,c_3746])).

cnf(c_19298,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_19253])).

cnf(c_19690,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_19298,c_4672])).

cnf(c_19744,plain,
    ( l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_19690,c_3971])).

cnf(c_24269,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_19744,c_4434])).

cnf(c_6929,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6882,c_3301])).

cnf(c_13974,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6929,c_3323])).

cnf(c_14080,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_13974])).

cnf(c_14532,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14080,c_3746])).

cnf(c_14599,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_14532])).

cnf(c_15008,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14599,c_4672])).

cnf(c_15891,plain,
    ( l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15008,c_3971])).

cnf(c_24253,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15891,c_4434])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_168])).

cnf(c_2741,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ iProver_ARSWP_113
    | arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_213])).

cnf(c_3302,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
    | r1_tarski(X0,X1) != iProver_top
    | iProver_ARSWP_113 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2741])).

cnf(c_8194,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_113 != iProver_top ),
    inference(superposition,[status(thm)],[c_3660,c_3302])).

cnf(c_13960,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_6929])).

cnf(c_14805,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_13960,c_4672])).

cnf(c_15750,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14805,c_3971])).

cnf(c_24091,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15750,c_4434])).

cnf(c_12,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2732,plain,
    ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_104 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_3309,plain,
    ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2732])).

cnf(c_4681,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_sK2_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_3309,c_3323])).

cnf(c_5376,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_4681,c_3301])).

cnf(c_10349,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_5376,c_3323])).

cnf(c_12037,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_10349])).

cnf(c_18137,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12037,c_4953])).

cnf(c_18156,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_18137,c_3301])).

cnf(c_23534,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18156,c_4953,c_5376])).

cnf(c_23535,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(renaming,[status(thm)],[c_23534])).

cnf(c_23552,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_23535,c_3323])).

cnf(c_23548,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_23535])).

cnf(c_23132,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_18056,c_3746])).

cnf(c_14520,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14080,c_4672])).

cnf(c_15526,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14520,c_3971])).

cnf(c_22797,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15526,c_3746])).

cnf(c_14077,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_13974])).

cnf(c_14424,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14077,c_4672])).

cnf(c_15401,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14424,c_3971])).

cnf(c_22587,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15401,c_4434])).

cnf(c_21164,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17076,c_3300])).

cnf(c_22451,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_21164])).

cnf(c_8252,plain,
    ( arAF0_k2_struct_0_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_5089])).

cnf(c_18151,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8252,c_18137])).

cnf(c_10345,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_5376])).

cnf(c_11219,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_10345,c_3323])).

cnf(c_22169,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18151,c_4953,c_11219])).

cnf(c_22170,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(renaming,[status(thm)],[c_22169])).

cnf(c_5374,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK2_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_4681,c_3300])).

cnf(c_10082,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK2_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_5374])).

cnf(c_19890,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK2_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(superposition,[status(thm)],[c_10082,c_4672])).

cnf(c_20038,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK2_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(superposition,[status(thm)],[c_19890,c_3971])).

cnf(c_22009,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK2_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(superposition,[status(thm)],[c_20038,c_4434])).

cnf(c_7750,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6921,c_3300])).

cnf(c_20159,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_7750])).

cnf(c_21832,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_20159,c_3971])).

cnf(c_7751,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6921,c_3316])).

cnf(c_17341,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_7751])).

cnf(c_21613,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17341,c_3746])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2729,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_101
    | arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 = arAF0_sK2_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_3312,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_101 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2729])).

cnf(c_5753,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_3312])).

cnf(c_16287,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5753,c_4672])).

cnf(c_16473,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_16287,c_3971])).

cnf(c_21594,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_16473,c_4434])).

cnf(c_6402,plain,
    ( arAF0_k2_struct_0_0 = sK7
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_4172])).

cnf(c_10346,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_5376])).

cnf(c_21069,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10346,c_4953])).

cnf(c_21084,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_6402,c_21069])).

cnf(c_21082,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_21069])).

cnf(c_14082,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_13974,c_4672])).

cnf(c_14870,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14082,c_3971])).

cnf(c_20899,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14870,c_4434])).

cnf(c_10,plain,
    ( r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2730,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_102
    | arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_3311,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_102 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2730])).

cnf(c_5092,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_3311])).

cnf(c_13695,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5092,c_4672])).

cnf(c_14698,plain,
    ( l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_13695,c_3971])).

cnf(c_20685,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14698,c_4434])).

cnf(c_9711,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_5091])).

cnf(c_3874,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3875,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3874])).

cnf(c_20236,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9711,c_3875,c_4953])).

cnf(c_5375,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_4681,c_3316])).

cnf(c_10312,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_5375])).

cnf(c_19008,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_10312,c_3746])).

cnf(c_19047,plain,
    ( arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_19008])).

cnf(c_19498,plain,
    ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_19047,c_4672])).

cnf(c_6877,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3310,c_4672])).

cnf(c_9454,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6877,c_3971])).

cnf(c_18869,plain,
    ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_9454,c_4434])).

cnf(c_9714,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8252,c_5091])).

cnf(c_9987,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8252,c_9716])).

cnf(c_4126,plain,
    ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X0))
    | r1_tarski(arAF0_k3_subset_1_0,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7914,plain,
    ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) ),
    inference(instantiation,[status(thm)],[c_4126])).

cnf(c_7915,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) != iProver_top
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7914])).

cnf(c_8178,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
    | ~ r1_tarski(arAF0_k4_xboole_0_0,arAF0_k4_xboole_0_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8179,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,arAF0_k4_xboole_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8178])).

cnf(c_9140,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8252,c_4953])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8132,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
    | X1 != k1_zfmisc_1(arAF0_k4_xboole_0_0)
    | X0 != arAF0_k4_xboole_0_0 ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_8431,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,X0)
    | ~ m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
    | X0 != k1_zfmisc_1(arAF0_k4_xboole_0_0)
    | arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0 ),
    inference(instantiation,[status(thm)],[c_8132])).

cnf(c_10890,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
    | ~ m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
    | k1_zfmisc_1(arAF0_k4_xboole_0_0) != k1_zfmisc_1(arAF0_k4_xboole_0_0)
    | arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0 ),
    inference(instantiation,[status(thm)],[c_8431])).

cnf(c_10891,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
    | ~ m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
    | arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_10890])).

cnf(c_10892,plain,
    ( arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10891])).

cnf(c_16412,plain,
    ( iProver_ARSWP_115 != iProver_top
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9987,c_7915,c_8179,c_8194,c_9140,c_10892])).

cnf(c_16413,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(renaming,[status(thm)],[c_16412])).

cnf(c_18664,plain,
    ( iProver_ARSWP_115 != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9714,c_8179,c_8194,c_9140,c_10892])).

cnf(c_18665,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(renaming,[status(thm)],[c_18664])).

cnf(c_18676,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_18665])).

cnf(c_18675,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_18665])).

cnf(c_9712,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_4173,c_5091])).

cnf(c_4403,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | ~ r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4404,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4403])).

cnf(c_5090,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_3316])).

cnf(c_18608,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9712,c_4404,c_5090])).

cnf(c_18620,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_18608])).

cnf(c_18154,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_18137,c_3316])).

cnf(c_18409,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18154,c_4953,c_5375])).

cnf(c_18424,plain,
    ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_18409])).

cnf(c_18152,plain,
    ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_6402,c_18137])).

cnf(c_18057,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17078,c_4434])).

cnf(c_3826,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(superposition,[status(thm)],[c_3660,c_3301])).

cnf(c_4065,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(superposition,[status(thm)],[c_3826,c_3323])).

cnf(c_6403,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_4065])).

cnf(c_26,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4246,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ iProver_ARSWP_115
    | arAF0_k3_subset_1_0 = arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_2743])).

cnf(c_4247,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k2_struct_0_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | iProver_ARSWP_115 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4246])).

cnf(c_3545,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK6))
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_4270,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK6))
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3545])).

cnf(c_4504,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_4270])).

cnf(c_4505,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_4504])).

cnf(c_4506,plain,
    ( arAF0_k3_subset_1_0 != sK7
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4505])).

cnf(c_4946,plain,
    ( X0 = arAF0_k3_subset_1_0
    | X0 != arAF0_k2_struct_0_0
    | arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_4055])).

cnf(c_6366,plain,
    ( arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0
    | arAF0_k2_struct_0_0 = arAF0_k3_subset_1_0
    | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_4946])).

cnf(c_6367,plain,
    ( arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0
    | arAF0_k2_struct_0_0 = arAF0_k3_subset_1_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6366])).

cnf(c_3639,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK6))
    | X0 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_8466,plain,
    ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(arAF0_k2_struct_0_0,X0)
    | X0 != k1_zfmisc_1(u1_struct_0(sK6))
    | arAF0_k2_struct_0_0 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_3639])).

cnf(c_13006,plain,
    ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | arAF0_k2_struct_0_0 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_8466])).

cnf(c_13007,plain,
    ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | arAF0_k2_struct_0_0 != arAF0_k3_subset_1_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13006])).

cnf(c_13008,plain,
    ( arAF0_k2_struct_0_0 != arAF0_k3_subset_1_0
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13007])).

cnf(c_4915,plain,
    ( ~ m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(X0))
    | r1_tarski(arAF0_k2_struct_0_0,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_13252,plain,
    ( ~ m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4915])).

cnf(c_13253,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13252])).

cnf(c_15050,plain,
    ( iProver_ARSWP_115 != iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6403,c_26,c_4172,c_4506,c_5089,c_6367,c_13008,c_13253])).

cnf(c_15051,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(renaming,[status(thm)],[c_15050])).

cnf(c_15060,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8252,c_15051])).

cnf(c_3796,plain,
    ( ~ m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3797,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3796])).

cnf(c_7648,plain,
    ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(arAF0_k4_xboole_0_0,X0)
    | X0 != k1_zfmisc_1(u1_struct_0(sK6))
    | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_3639])).

cnf(c_12985,plain,
    ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_7648])).

cnf(c_12986,plain,
    ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_12985])).

cnf(c_12987,plain,
    ( arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12986])).

cnf(c_17540,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15060,c_26,c_3797,c_4172,c_4506,c_5873,c_8194,c_12987])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2734,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_106
    | ~ arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_14])).

cnf(c_3308,plain,
    ( arAF0_k9_subset_1_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2734])).

cnf(c_6489,plain,
    ( arAF0_k9_subset_1_0 = X0
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3324,c_3308])).

cnf(c_17551,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_17540,c_6489])).

cnf(c_17924,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_17551])).

cnf(c_17308,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_17297])).

cnf(c_9715,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_6402,c_5091])).

cnf(c_6081,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7))
    | ~ r1_tarski(arAF0_k3_subset_1_0,sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6082,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
    | r1_tarski(arAF0_k3_subset_1_0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6081])).

cnf(c_9988,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_6402,c_9716])).

cnf(c_7065,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK7,sK7)
    | X0 != sK7
    | X1 != sK7 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_7229,plain,
    ( r1_tarski(X0,sK7)
    | ~ r1_tarski(sK7,sK7)
    | X0 != sK7
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_7065])).

cnf(c_7230,plain,
    ( r1_tarski(X0,sK7)
    | ~ r1_tarski(sK7,sK7)
    | X0 != sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_7229])).

cnf(c_7247,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,sK7)
    | ~ r1_tarski(sK7,sK7)
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_7230])).

cnf(c_7248,plain,
    ( arAF0_k3_subset_1_0 != sK7
    | r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
    | r1_tarski(sK7,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7247])).

cnf(c_7307,plain,
    ( r1_tarski(sK7,sK7) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_6402,c_4953])).

cnf(c_15193,plain,
    ( iProver_ARSWP_115 != iProver_top
    | r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9988,c_4172,c_7248,c_7307])).

cnf(c_15194,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(renaming,[status(thm)],[c_15193])).

cnf(c_16860,plain,
    ( iProver_ARSWP_115 != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9715,c_4172,c_6082,c_7248,c_7307])).

cnf(c_16861,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(renaming,[status(thm)],[c_16860])).

cnf(c_16872,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_4173,c_16861])).

cnf(c_16871,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_16861])).

cnf(c_16870,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_16861])).

cnf(c_16424,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_16413])).

cnf(c_6404,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_3826])).

cnf(c_7504,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_6404,c_3308])).

cnf(c_15064,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_15051,c_6489])).

cnf(c_16265,plain,
    ( iProver_ARSWP_115 != iProver_top
    | arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7504,c_4783,c_15064])).

cnf(c_16266,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(renaming,[status(thm)],[c_16265])).

cnf(c_9986,plain,
    ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_9716])).

cnf(c_3647,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_3850,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3647])).

cnf(c_3851,plain,
    ( X0 != sK7
    | sK7 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3850])).

cnf(c_4268,plain,
    ( arAF0_k3_subset_1_0 != sK7
    | sK7 = arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_3851])).

cnf(c_4522,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k2_struct_0_0
    | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_3873])).

cnf(c_4523,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k2_struct_0_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4522])).

cnf(c_5489,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_4523])).

cnf(c_5490,plain,
    ( arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5489])).

cnf(c_4107,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k3_subset_1_0
    | X1 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_4879,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k3_subset_1_0
    | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_4107])).

cnf(c_4880,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k3_subset_1_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4879])).

cnf(c_6126,plain,
    ( ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
    | r1_tarski(sK7,arAF0_k2_struct_0_0)
    | sK7 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_4880])).

cnf(c_6127,plain,
    ( sK7 != arAF0_k3_subset_1_0
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6126])).

cnf(c_10702,plain,
    ( iProver_ARSWP_115 != iProver_top
    | r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9986,c_4172,c_4268,c_4953,c_5089,c_5490,c_6127])).

cnf(c_10703,plain,
    ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(renaming,[status(thm)],[c_10702])).

cnf(c_15952,plain,
    ( r1_tarski(sK7,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_10703])).

cnf(c_9713,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_5091])).

cnf(c_5242,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | ~ r1_tarski(sK7,arAF0_k2_struct_0_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5243,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | r1_tarski(sK7,arAF0_k2_struct_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5242])).

cnf(c_11011,plain,
    ( iProver_ARSWP_115 != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9713,c_4172,c_4268,c_4953,c_5089,c_5243,c_5490,c_6127])).

cnf(c_11012,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(renaming,[status(thm)],[c_11011])).

cnf(c_15950,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_11012])).

cnf(c_15962,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_4953])).

cnf(c_15530,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14520,c_3746])).

cnf(c_15204,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,sK7) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_15194])).

cnf(c_15203,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,sK7) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_15194])).

cnf(c_13292,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,sK7) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_6402,c_5090])).

cnf(c_8256,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_4065])).

cnf(c_8551,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8256,c_6489])).

cnf(c_13081,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_8551])).

cnf(c_6926,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6882,c_3300])).

cnf(c_12750,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_6926])).

cnf(c_17077,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7749,c_3300])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2736,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_108
    | ~ arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_16])).

cnf(c_3307,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2736])).

cnf(c_5321,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_3307])).

cnf(c_5545,plain,
    ( r1_tarski(arAF0_sK4_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5321,c_3323])).

cnf(c_5564,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5545,c_3316])).

cnf(c_5900,plain,
    ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_5564])).

cnf(c_3596,plain,
    ( ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_20,c_4])).

cnf(c_3597,plain,
    ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3596])).

cnf(c_5935,plain,
    ( r1_tarski(sK7,u1_struct_0(sK5)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(instantiation,[status(thm)],[c_5900])).

cnf(c_12003,plain,
    ( arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5900,c_3597,c_5935])).

cnf(c_12014,plain,
    ( iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_12003])).

cnf(c_10348,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_5376])).

cnf(c_11280,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_10348,c_3322])).

cnf(c_11574,plain,
    ( arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_4953,c_11280])).

cnf(c_11644,plain,
    ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_98 != iProver_top ),
    inference(superposition,[status(thm)],[c_11574,c_4672])).

cnf(c_11277,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_104 != iProver_top ),
    inference(superposition,[status(thm)],[c_10348,c_3323])).

cnf(c_11022,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_6402,c_11012])).

cnf(c_11021,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8252,c_11012])).

cnf(c_10712,plain,
    ( r1_tarski(sK7,arAF0_k4_xboole_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8252,c_10703])).

cnf(c_10347,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_4173,c_5376])).

cnf(c_9983,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_9716])).

cnf(c_9710,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_5091])).

cnf(c_4291,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(superposition,[status(thm)],[c_4173,c_3826])).

cnf(c_3622,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3623,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3622])).

cnf(c_5075,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_97 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4291,c_3623,c_3904])).

cnf(c_6493,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5075,c_3308])).

cnf(c_9492,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | iProver_ARSWP_97 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_6493])).

cnf(c_8257,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_3826])).

cnf(c_5565,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5545,c_3301])).

cnf(c_8254,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_5565])).

cnf(c_5948,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5565,c_3323])).

cnf(c_8253,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_5948])).

cnf(c_8255,plain,
    ( arAF0_k4_xboole_0_0 = sK7
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_4172])).

cnf(c_17080,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7749,c_3301])).

cnf(c_7753,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_98 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6921,c_3301])).

cnf(c_6494,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(X0) != iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5321,c_3308])).

cnf(c_7131,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_6494])).

cnf(c_7729,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7131,c_4783])).

cnf(c_6492,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3826,c_3308])).

cnf(c_7282,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_6492])).

cnf(c_6490,plain,
    ( arAF0_k9_subset_1_0 = sK7
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_3308])).

cnf(c_6720,plain,
    ( arAF0_k9_subset_1_0 = sK7
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_106 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_6490])).

cnf(c_5947,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_5565])).

cnf(c_27,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5996,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(instantiation,[status(thm)],[c_5947])).

cnf(c_6138,plain,
    ( arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5947,c_27,c_5996])).

cnf(c_6147,plain,
    ( iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_6138])).

cnf(c_5563,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK4_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5545,c_3300])).

cnf(c_5763,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK4_0
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_5563])).

cnf(c_5320,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
    | arAF0_sP0_0_1(X2) != iProver_top
    | iProver_ARSWP_108 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3324,c_3307])).

cnf(c_3978,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top ),
    inference(superposition,[status(thm)],[c_3303,c_3971])).

cnf(c_4442,plain,
    ( arAF0_sP1_0_1(sK6) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top ),
    inference(superposition,[status(thm)],[c_3978,c_4434])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(sK2(X2,X1),u1_pre_topc(X2))
    | sP0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)) != sK2(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2728,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X2)
    | ~ iProver_ARSWP_100
    | ~ arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 != arAF0_sK2_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_3313,plain,
    ( arAF0_k9_subset_1_0 != arAF0_sK2_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X2) = iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2728])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.90/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.90/1.50  
% 7.90/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.90/1.50  
% 7.90/1.50  ------  iProver source info
% 7.90/1.50  
% 7.90/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.90/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.90/1.50  git: non_committed_changes: false
% 7.90/1.50  git: last_make_outside_of_git: false
% 7.90/1.50  
% 7.90/1.50  ------ 
% 7.90/1.50  ------ Parsing...
% 7.90/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.90/1.50  ------ Proving...
% 7.90/1.50  ------ Problem Properties 
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  clauses                                 24
% 7.90/1.50  conjectures                             4
% 7.90/1.50  EPR                                     6
% 7.90/1.50  Horn                                    20
% 7.90/1.50  unary                                   4
% 7.90/1.50  binary                                  7
% 7.90/1.50  lits                                    68
% 7.90/1.50  lits eq                                 5
% 7.90/1.50  fd_pure                                 0
% 7.90/1.50  fd_pseudo                               0
% 7.90/1.50  fd_cond                                 0
% 7.90/1.50  fd_pseudo_cond                          0
% 7.90/1.50  AC symbols                              0
% 7.90/1.50  
% 7.90/1.50  ------ Input Options Time Limit: Unbounded
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing...
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.90/1.50  Current options:
% 7.90/1.50  ------ 
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  ------ Proving...
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing...
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing...
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing...
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.90/1.50  
% 7.90/1.50  ------ Proving...
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.90/1.50  
% 7.90/1.50  ------ Proving...
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.90/1.50  
% 7.90/1.50  ------ Proving...
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.90/1.50  
% 7.90/1.50  ------ Proving...
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.90/1.50  
% 7.90/1.50  ------ Proving...
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.90/1.50  
% 7.90/1.50  ------ Proving...
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.90/1.50  
% 7.90/1.50  ------ Proving...
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.90/1.50  
% 7.90/1.50  ------ Proving...
% 7.90/1.50  
% 7.90/1.50  
% 7.90/1.50  % SZS status CounterSatisfiable for theBenchmark.p
% 7.90/1.50  
% 7.90/1.50  % SZS output start Saturation for theBenchmark.p
% 7.90/1.50  
% 7.90/1.50  fof(f9,conjecture,(
% 7.90/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.90/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.90/1.50  
% 7.90/1.50  fof(f10,negated_conjecture,(
% 7.90/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.90/1.50    inference(negated_conjecture,[],[f9])).
% 7.90/1.50  
% 7.90/1.50  fof(f18,plain,(
% 7.90/1.50    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 7.90/1.50    inference(ennf_transformation,[],[f10])).
% 7.90/1.50  
% 7.90/1.50  fof(f33,plain,(
% 7.90/1.50    ( ! [X0,X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.90/1.50    introduced(choice_axiom,[])).
% 7.90/1.50  
% 7.90/1.50  fof(f32,plain,(
% 7.90/1.50    ( ! [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) => (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_pre_topc(sK6,X0))) )),
% 7.90/1.50    introduced(choice_axiom,[])).
% 7.90/1.50  
% 7.90/1.50  fof(f31,plain,(
% 7.90/1.50    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,sK5)) & l1_pre_topc(sK5))),
% 7.90/1.50    introduced(choice_axiom,[])).
% 7.90/1.50  
% 7.90/1.50  fof(f34,plain,(
% 7.90/1.50    ((~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_pre_topc(sK6,sK5)) & l1_pre_topc(sK5)),
% 7.90/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f18,f33,f32,f31])).
% 7.90/1.50  
% 7.90/1.50  fof(f57,plain,(
% 7.90/1.50    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 7.90/1.50    inference(cnf_transformation,[],[f34])).
% 7.90/1.50  
% 7.90/1.50  fof(f5,axiom,(
% 7.90/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.90/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.90/1.50  
% 7.90/1.50  fof(f22,plain,(
% 7.90/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.90/1.50    inference(nnf_transformation,[],[f5])).
% 7.90/1.50  
% 7.90/1.50  fof(f39,plain,(
% 7.90/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.90/1.50    inference(cnf_transformation,[],[f22])).
% 7.90/1.50  
% 7.90/1.50  fof(f4,axiom,(
% 7.90/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.90/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.90/1.50  
% 7.90/1.50  fof(f15,plain,(
% 7.90/1.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.90/1.50    inference(ennf_transformation,[],[f4])).
% 7.90/1.50  
% 7.90/1.50  fof(f38,plain,(
% 7.90/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.90/1.50    inference(cnf_transformation,[],[f15])).
% 7.90/1.50  
% 7.90/1.50  fof(f40,plain,(
% 7.90/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.90/1.50    inference(cnf_transformation,[],[f22])).
% 7.90/1.50  
% 7.90/1.50  fof(f1,axiom,(
% 7.90/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 7.90/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.90/1.50  
% 7.90/1.50  fof(f12,plain,(
% 7.90/1.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 7.90/1.50    inference(ennf_transformation,[],[f1])).
% 7.90/1.50  
% 7.90/1.50  fof(f35,plain,(
% 7.90/1.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 7.90/1.50    inference(cnf_transformation,[],[f12])).
% 7.90/1.50  
% 7.90/1.50  fof(f19,plain,(
% 7.90/1.50    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 7.90/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.90/1.50  
% 7.90/1.50  fof(f24,plain,(
% 7.90/1.50    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.90/1.50    inference(nnf_transformation,[],[f19])).
% 7.90/1.50  
% 7.90/1.50  fof(f25,plain,(
% 7.90/1.50    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.90/1.50    inference(flattening,[],[f24])).
% 7.90/1.50  
% 7.90/1.50  fof(f26,plain,(
% 7.90/1.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.90/1.50    inference(rectify,[],[f25])).
% 7.90/1.50  
% 7.90/1.50  fof(f29,plain,(
% 7.90/1.50    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.90/1.50    introduced(choice_axiom,[])).
% 7.90/1.50  
% 7.90/1.50  fof(f28,plain,(
% 7.90/1.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 7.90/1.50    introduced(choice_axiom,[])).
% 7.90/1.50  
% 7.90/1.50  fof(f27,plain,(
% 7.90/1.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.90/1.50    introduced(choice_axiom,[])).
% 7.90/1.50  
% 7.90/1.50  fof(f30,plain,(
% 7.90/1.50    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.90/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f29,f28,f27])).
% 7.90/1.50  
% 7.90/1.50  fof(f49,plain,(
% 7.90/1.50    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.90/1.50    inference(cnf_transformation,[],[f30])).
% 7.90/1.50  
% 7.90/1.50  fof(f55,plain,(
% 7.90/1.50    l1_pre_topc(sK5)),
% 7.90/1.50    inference(cnf_transformation,[],[f34])).
% 7.90/1.50  
% 7.90/1.50  fof(f6,axiom,(
% 7.90/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 7.90/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.90/1.50  
% 7.90/1.50  fof(f16,plain,(
% 7.90/1.50    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.90/1.50    inference(ennf_transformation,[],[f6])).
% 7.90/1.50  
% 7.90/1.50  fof(f20,plain,(
% 7.90/1.50    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 7.90/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.90/1.50  
% 7.90/1.50  fof(f21,plain,(
% 7.90/1.50    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.90/1.50    inference(definition_folding,[],[f16,f20,f19])).
% 7.90/1.50  
% 7.90/1.50  fof(f53,plain,(
% 7.90/1.50    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.90/1.50    inference(cnf_transformation,[],[f21])).
% 7.90/1.50  
% 7.90/1.50  fof(f23,plain,(
% 7.90/1.50    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 7.90/1.50    inference(nnf_transformation,[],[f20])).
% 7.90/1.50  
% 7.90/1.50  fof(f42,plain,(
% 7.90/1.50    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 7.90/1.50    inference(cnf_transformation,[],[f23])).
% 7.90/1.50  
% 7.90/1.50  fof(f8,axiom,(
% 7.90/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.90/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.90/1.50  
% 7.90/1.50  fof(f17,plain,(
% 7.90/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.90/1.50    inference(ennf_transformation,[],[f8])).
% 7.90/1.50  
% 7.90/1.50  fof(f54,plain,(
% 7.90/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.90/1.50    inference(cnf_transformation,[],[f17])).
% 7.90/1.50  
% 7.90/1.50  fof(f58,plain,(
% 7.90/1.50    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))),
% 7.90/1.50    inference(cnf_transformation,[],[f34])).
% 7.90/1.50  
% 7.90/1.50  fof(f3,axiom,(
% 7.90/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.90/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.90/1.50  
% 7.90/1.50  fof(f14,plain,(
% 7.90/1.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.90/1.50    inference(ennf_transformation,[],[f3])).
% 7.90/1.50  
% 7.90/1.50  fof(f37,plain,(
% 7.90/1.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.90/1.50    inference(cnf_transformation,[],[f14])).
% 7.90/1.50  
% 7.90/1.50  fof(f56,plain,(
% 7.90/1.50    m1_pre_topc(sK6,sK5)),
% 7.90/1.50    inference(cnf_transformation,[],[f34])).
% 7.90/1.50  
% 7.90/1.50  fof(f41,plain,(
% 7.90/1.50    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 7.90/1.50    inference(cnf_transformation,[],[f23])).
% 7.90/1.50  
% 7.90/1.50  fof(f43,plain,(
% 7.90/1.50    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 7.90/1.50    inference(cnf_transformation,[],[f30])).
% 7.90/1.50  
% 7.90/1.50  fof(f2,axiom,(
% 7.90/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.90/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.90/1.50  
% 7.90/1.50  fof(f13,plain,(
% 7.90/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.90/1.50    inference(ennf_transformation,[],[f2])).
% 7.90/1.50  
% 7.90/1.50  fof(f36,plain,(
% 7.90/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.90/1.50    inference(cnf_transformation,[],[f13])).
% 7.90/1.50  
% 7.90/1.50  fof(f48,plain,(
% 7.90/1.50    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.90/1.50    inference(cnf_transformation,[],[f30])).
% 7.90/1.50  
% 7.90/1.50  fof(f51,plain,(
% 7.90/1.50    ( ! [X0,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.90/1.50    inference(cnf_transformation,[],[f30])).
% 7.90/1.50  
% 7.90/1.50  fof(f50,plain,(
% 7.90/1.50    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.90/1.50    inference(cnf_transformation,[],[f30])).
% 7.90/1.50  
% 7.90/1.50  fof(f46,plain,(
% 7.90/1.50    ( ! [X0,X5,X1] : (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 7.90/1.50    inference(cnf_transformation,[],[f30])).
% 7.90/1.50  
% 7.90/1.50  fof(f44,plain,(
% 7.90/1.50    ( ! [X0,X5,X1] : (m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 7.90/1.50    inference(cnf_transformation,[],[f30])).
% 7.90/1.50  
% 7.90/1.50  fof(f52,plain,(
% 7.90/1.50    ( ! [X0,X3,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.90/1.50    inference(cnf_transformation,[],[f30])).
% 7.90/1.50  
% 7.90/1.50  cnf(c_272,plain,( X0_2 = X0_2 ),theory(equality) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_21,negated_conjecture,
% 7.90/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 7.90/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3321,plain,
% 7.90/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_5,plain,
% 7.90/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.90/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3323,plain,
% 7.90/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.90/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3660,plain,
% 7.90/1.50      ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_3321,c_3323]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3,plain,
% 7.90/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.90/1.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.90/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4,plain,
% 7.90/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.90/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_167,plain,
% 7.90/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.90/1.50      inference(prop_impl,[status(thm)],[c_4]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_168,plain,
% 7.90/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.90/1.50      inference(renaming,[status(thm)],[c_167]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_215,plain,
% 7.90/1.50      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.90/1.50      inference(bin_hyper_res,[status(thm)],[c_3,c_168]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2743,plain,
% 7.90/1.50      ( ~ r1_tarski(X0,X1) | ~ iProver_ARSWP_115 | arAF0_k3_subset_1_0 = X0 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_215]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3300,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = X0
% 7.90/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2743]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4172,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = sK7 | iProver_ARSWP_115 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_3660,c_3300]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_0,plain,
% 7.90/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1) ),
% 7.90/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2725,plain,
% 7.90/1.50      ( ~ r1_tarski(X0,X1)
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,X1)
% 7.90/1.50      | ~ iProver_ARSWP_97 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3316,plain,
% 7.90/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2725]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3904,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_3660,c_3316]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4173,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_3904,c_3300]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4288,plain,
% 7.90/1.50      ( arAF0_k4_xboole_0_0 = sK7
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4172,c_4173]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_11,plain,
% 7.90/1.50      ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 7.90/1.50      | sP0(X0,X1)
% 7.90/1.50      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
% 7.90/1.50      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.90/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2731,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
% 7.90/1.50      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.50      | arAF0_sP0_0_1(X1)
% 7.90/1.50      | ~ iProver_ARSWP_103
% 7.90/1.50      | arAF0_r2_hidden_0 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3310,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2731]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_6882,plain,
% 7.90/1.50      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_3310,c_3323]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_23,negated_conjecture,
% 7.90/1.50      ( l1_pre_topc(sK5) ),
% 7.90/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3320,plain,
% 7.90/1.50      ( l1_pre_topc(sK5) = iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_18,plain,
% 7.90/1.50      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 7.90/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2738,plain,
% 7.90/1.50      ( arAF0_sP1_0_1(X0)
% 7.90/1.50      | ~ l1_pre_topc(X0)
% 7.90/1.50      | ~ l1_pre_topc(X1)
% 7.90/1.50      | ~ iProver_ARSWP_110 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_18]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3305,plain,
% 7.90/1.50      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.50      | l1_pre_topc(X1) != iProver_top
% 7.90/1.50      | l1_pre_topc(X0) != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2738]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3686,plain,
% 7.90/1.50      ( arAF0_sP1_0_1(X0) | ~ l1_pre_topc(X0) | ~ iProver_ARSWP_110 ),
% 7.90/1.50      inference(resolution,[status(thm)],[c_2738,c_23]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3687,plain,
% 7.90/1.50      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.50      | l1_pre_topc(X0) != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_3686]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4434,plain,
% 7.90/1.50      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.50      | l1_pre_topc(X0) != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top ),
% 7.90/1.50      inference(global_propositional_subsumption,[status(thm)],[c_3305,c_3687]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4441,plain,
% 7.90/1.50      ( arAF0_sP1_0_1(sK5) = iProver_top | iProver_ARSWP_110 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_3320,c_4434]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_6,plain,
% 7.90/1.50      ( ~ sP1(X0,X1) | ~ sP0(X1,X0) | m1_pre_topc(X1,X0) ),
% 7.90/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2726,plain,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(X0)
% 7.90/1.50      | ~ arAF0_sP0_0_1(X0)
% 7.90/1.50      | ~ arAF0_sP1_0_1(X1)
% 7.90/1.50      | ~ iProver_ARSWP_98 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3315,plain,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) != iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X1) != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2726]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4672,plain,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4441,c_3315]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_6921,plain,
% 7.90/1.50      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_6882,c_4672]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_19,plain,
% 7.90/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.90/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2739,plain,
% 7.90/1.50      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 7.90/1.50      | ~ l1_pre_topc(X1)
% 7.90/1.50      | l1_pre_topc(X0)
% 7.90/1.50      | ~ iProver_ARSWP_111 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_19]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3304,plain,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.90/1.50      | l1_pre_topc(X1) != iProver_top
% 7.90/1.50      | l1_pre_topc(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2739]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3770,plain,
% 7.90/1.50      ( ~ arAF0_m1_pre_topc_0_1(X0) | l1_pre_topc(X0) | ~ iProver_ARSWP_111 ),
% 7.90/1.50      inference(resolution,[status(thm)],[c_2739,c_23]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3771,plain,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.90/1.50      | l1_pre_topc(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_3770]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3971,plain,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.90/1.50      | l1_pre_topc(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top ),
% 7.90/1.50      inference(global_propositional_subsumption,[status(thm)],[c_3304,c_3771]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_7749,plain,
% 7.90/1.50      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | l1_pre_topc(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_6921,c_3971]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_17078,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | l1_pre_topc(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_7749,c_3316]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_18056,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | l1_pre_topc(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4288,c_17078]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_23128,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_18056,c_4434]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3324,plain,
% 7.90/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.90/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_20,negated_conjecture,
% 7.90/1.50      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.90/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3322,plain,
% 7.90/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3746,plain,
% 7.90/1.50      ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_3324,c_3322]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_27575,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_23128,c_3746]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_17076,plain,
% 7.90/1.50      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_7749,c_4434]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2,plain,
% 7.90/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.90/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.90/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_214,plain,
% 7.90/1.50      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~ r1_tarski(X1,X0) ),
% 7.90/1.50      inference(bin_hyper_res,[status(thm)],[c_2,c_168]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2742,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X0))
% 7.90/1.50      | ~ r1_tarski(X1,X0)
% 7.90/1.50      | ~ iProver_ARSWP_114 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_214]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3301,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X0)) = iProver_top
% 7.90/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2742]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_21167,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_17076,c_3301]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_25964,plain,
% 7.90/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4172,c_21167]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_26305,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_25964,c_3322]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_22,negated_conjecture,
% 7.90/1.50      ( m1_pre_topc(sK6,sK5) ),
% 7.90/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2740,negated_conjecture,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(sK6) | ~ iProver_ARSWP_112 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_22]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3303,plain,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(sK6) = iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2740]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_7,plain,
% 7.90/1.50      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 7.90/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2727,plain,
% 7.90/1.50      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 7.90/1.50      | arAF0_sP0_0_1(X0)
% 7.90/1.50      | ~ arAF0_sP1_0_1(X1)
% 7.90/1.50      | ~ iProver_ARSWP_99 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3314,plain,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X1) != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2727]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4567,plain,
% 7.90/1.50      ( arAF0_sP0_0_1(sK6) = iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X0) != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_3303,c_3314]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4783,plain,
% 7.90/1.50      ( arAF0_sP0_0_1(sK6) = iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4441,c_4567]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_17,plain,
% 7.90/1.50      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.90/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2737,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.50      | ~ arAF0_sP0_0_1(X0)
% 7.90/1.50      | ~ iProver_ARSWP_109 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_17]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3306,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2737]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4953,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4783,c_3306]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_5089,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_k2_struct_0_0
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4953,c_3300]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_6401,plain,
% 7.90/1.50      ( arAF0_k2_struct_0_0 = arAF0_k4_xboole_0_0
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_5089,c_4173]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_5091,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4953,c_3301]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_15957,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_6401,c_5091]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_13263,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
% 7.90/1.50      | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) ),
% 7.90/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_13264,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_13263]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_9716,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_5091,c_3323]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_15956,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_6401,c_9716]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_286,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4055,plain,
% 7.90/1.50      ( X0 != X1 | X0 = arAF0_k3_subset_1_0 | arAF0_k3_subset_1_0 != X1 ),
% 7.90/1.50      inference(instantiation,[status(thm)],[c_286]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4728,plain,
% 7.90/1.50      ( X0 = arAF0_k3_subset_1_0
% 7.90/1.50      | X0 != arAF0_k4_xboole_0_0
% 7.90/1.50      | arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0 ),
% 7.90/1.50      inference(instantiation,[status(thm)],[c_4055]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_5872,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0
% 7.90/1.50      | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
% 7.90/1.50      | arAF0_k4_xboole_0_0 != arAF0_k4_xboole_0_0 ),
% 7.90/1.50      inference(instantiation,[status(thm)],[c_4728]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_5873,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0
% 7.90/1.50      | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0 ),
% 7.90/1.50      inference(equality_resolution_simp,[status(thm)],[c_5872]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_287,plain,
% 7.90/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.90/1.50      theory(equality) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3873,plain,
% 7.90/1.50      ( r1_tarski(X0,X1)
% 7.90/1.50      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.50      | X0 != arAF0_k2_struct_0_0
% 7.90/1.50      | X1 != arAF0_k2_struct_0_0 ),
% 7.90/1.50      inference(instantiation,[status(thm)],[c_287]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4937,plain,
% 7.90/1.50      ( r1_tarski(X0,arAF0_k3_subset_1_0)
% 7.90/1.50      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.50      | X0 != arAF0_k2_struct_0_0
% 7.90/1.50      | arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0 ),
% 7.90/1.50      inference(instantiation,[status(thm)],[c_3873]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_6333,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
% 7.90/1.50      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.50      | arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0 ),
% 7.90/1.50      inference(instantiation,[status(thm)],[c_4937]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_6334,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0
% 7.90/1.50      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_6333]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_5726,plain,
% 7.90/1.50      ( r1_tarski(X0,X1)
% 7.90/1.50      | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
% 7.90/1.50      | X0 != arAF0_k3_subset_1_0
% 7.90/1.50      | X1 != arAF0_k3_subset_1_0 ),
% 7.90/1.50      inference(instantiation,[status(thm)],[c_287]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_7675,plain,
% 7.90/1.50      ( r1_tarski(X0,arAF0_k4_xboole_0_0)
% 7.90/1.50      | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
% 7.90/1.50      | X0 != arAF0_k3_subset_1_0
% 7.90/1.50      | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
% 7.90/1.50      inference(instantiation,[status(thm)],[c_5726]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_10263,plain,
% 7.90/1.50      ( ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
% 7.90/1.50      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0)
% 7.90/1.50      | arAF0_k3_subset_1_0 != arAF0_k3_subset_1_0
% 7.90/1.50      | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
% 7.90/1.50      inference(instantiation,[status(thm)],[c_7675]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_10264,plain,
% 7.90/1.50      ( ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
% 7.90/1.50      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0)
% 7.90/1.50      | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
% 7.90/1.50      inference(equality_resolution_simp,[status(thm)],[c_10263]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_10265,plain,
% 7.90/1.50      ( arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0
% 7.90/1.50      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_10264]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_17296,plain,
% 7.90/1.50      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(global_propositional_subsumption,
% 7.90/1.50                [status(thm)],
% 7.90/1.50                [c_15956,c_4173,c_4953,c_5089,c_5873,c_6334,c_10265]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_17297,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(renaming,[status(thm)],[c_17296]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_25744,plain,
% 7.90/1.50      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(global_propositional_subsumption,
% 7.90/1.50                [status(thm)],
% 7.90/1.50                [c_15957,c_13264,c_17297]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_25745,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(renaming,[status(thm)],[c_25744]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_25756,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_5089,c_25745]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_6927,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_6882,c_3316]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_13629,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4288,c_6927]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_19253,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_13629,c_3746]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_19298,plain,
% 7.90/1.50      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4953,c_19253]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_19690,plain,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_19298,c_4672]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_19744,plain,
% 7.90/1.50      ( l1_pre_topc(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_19690,c_3971]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_24269,plain,
% 7.90/1.50      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_19744,c_4434]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_6929,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_6882,c_3301]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_13974,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_6929,c_3323]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_14080,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4172,c_13974]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_14532,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_14080,c_3746]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_14599,plain,
% 7.90/1.50      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4953,c_14532]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_15008,plain,
% 7.90/1.50      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_14599,c_4672]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_15891,plain,
% 7.90/1.50      ( l1_pre_topc(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_15008,c_3971]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_24253,plain,
% 7.90/1.50      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_15891,c_4434]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_1,plain,
% 7.90/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.90/1.50      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.90/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_213,plain,
% 7.90/1.50      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.90/1.50      inference(bin_hyper_res,[status(thm)],[c_1,c_168]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2741,plain,
% 7.90/1.50      ( ~ r1_tarski(X0,X1)
% 7.90/1.50      | ~ iProver_ARSWP_113
% 7.90/1.50      | arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_213]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3302,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
% 7.90/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2741]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_8194,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_3660,c_3302]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_13960,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_8194,c_6929]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_14805,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_13960,c_4672]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_15750,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | l1_pre_topc(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_14805,c_3971]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_24091,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_15750,c_4434]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_12,plain,
% 7.90/1.50      ( sP0(X0,X1)
% 7.90/1.50      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.90/1.50      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.90/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2732,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0)))
% 7.90/1.50      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.50      | arAF0_sP0_0_1(X0)
% 7.90/1.50      | ~ iProver_ARSWP_104 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3309,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2732]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_4681,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_sK2_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_3309,c_3323]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_5376,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4681,c_3301]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_10349,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_5376,c_3323]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_12037,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_5089,c_10349]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_18137,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(global_propositional_subsumption,
% 7.90/1.50                [status(thm)],
% 7.90/1.50                [c_12037,c_4953]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_18156,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_18137,c_3301]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_23534,plain,
% 7.90/1.50      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(global_propositional_subsumption,
% 7.90/1.50                [status(thm)],
% 7.90/1.50                [c_18156,c_4953,c_5376]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_23535,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(renaming,[status(thm)],[c_23534]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_23552,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_23535,c_3323]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_23548,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_8194,c_23535]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_23132,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | l1_pre_topc(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_18056,c_3746]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_14520,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_14080,c_4672]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_15526,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | l1_pre_topc(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_14520,c_3971]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_22797,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | l1_pre_topc(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_15526,c_3746]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_14077,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_8194,c_13974]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_14424,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_14077,c_4672]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_15401,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | l1_pre_topc(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_14424,c_3971]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_22587,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_15401,c_4434]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_21164,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_17076,c_3300]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_22451,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.90/1.50      | arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4953,c_21164]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_8252,plain,
% 7.90/1.50      ( arAF0_k2_struct_0_0 = arAF0_k4_xboole_0_0
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_8194,c_5089]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_18151,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_8252,c_18137]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_10345,plain,
% 7.90/1.50      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_8194,c_5376]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_11219,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_10345,c_3323]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_22169,plain,
% 7.90/1.50      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(global_propositional_subsumption,
% 7.90/1.50                [status(thm)],
% 7.90/1.50                [c_18151,c_4953,c_11219]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_22170,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_114 != iProver_top
% 7.90/1.50      | iProver_ARSWP_113 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(renaming,[status(thm)],[c_22169]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_5374,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_sK2_0
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4681,c_3300]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_10082,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_sK2_0
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4953,c_5374]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_19890,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_sK2_0
% 7.90/1.50      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_10082,c_4672]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_20038,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_sK2_0
% 7.90/1.50      | l1_pre_topc(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_19890,c_3971]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_22009,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_sK2_0
% 7.90/1.50      | arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_104 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_20038,c_4434]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_7750,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_6921,c_3300]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_20159,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.90/1.50      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4953,c_7750]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_21832,plain,
% 7.90/1.50      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.90/1.50      | l1_pre_topc(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_111 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_99 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_20159,c_3971]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_7751,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_6921,c_3316]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_17341,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.50      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_4288,c_7751]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_21613,plain,
% 7.90/1.50      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_115 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_103 != iProver_top
% 7.90/1.50      | iProver_ARSWP_98 != iProver_top
% 7.90/1.50      | iProver_ARSWP_97 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(superposition,[status(thm)],[c_17341,c_3746]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_9,plain,
% 7.90/1.50      ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 7.90/1.50      | sP0(X0,X1)
% 7.90/1.50      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
% 7.90/1.50      | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) ),
% 7.90/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_2729,plain,
% 7.90/1.50      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.50      | arAF0_sP0_0_1(X0)
% 7.90/1.50      | ~ iProver_ARSWP_101
% 7.90/1.50      | arAF0_r2_hidden_0
% 7.90/1.50      | arAF0_k9_subset_1_0 = arAF0_sK2_0 ),
% 7.90/1.50      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_3312,plain,
% 7.90/1.50      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.90/1.50      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_101 != iProver_top
% 7.90/1.50      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.50      inference(predicate_to_equality,[status(thm)],[c_2729]) ).
% 7.90/1.50  
% 7.90/1.50  cnf(c_5753,plain,
% 7.90/1.50      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.90/1.50      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.50      | iProver_ARSWP_112 != iProver_top
% 7.90/1.50      | iProver_ARSWP_110 != iProver_top
% 7.90/1.50      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_101 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4953,c_3312]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16287,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.90/1.51      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_101 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5753,c_4672]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16473,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.90/1.51      | l1_pre_topc(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_101 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_16287,c_3971]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_21594,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.90/1.51      | arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_101 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_16473,c_4434]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6402,plain,
% 7.90/1.51      ( arAF0_k2_struct_0_0 = sK7
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5089,c_4172]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10346,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5089,c_5376]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_21069,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_10346,c_4953]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_21084,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6402,c_21069]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_21082,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6401,c_21069]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_14082,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_13974,c_4672]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_14870,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | l1_pre_topc(X1) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_14082,c_3971]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_20899,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_sP1_0_1(X1) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_14870,c_4434]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10,plain,
% 7.90/1.51      ( r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
% 7.90/1.51      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 7.90/1.51      | sP0(X0,X1)
% 7.90/1.51      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.90/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_2730,plain,
% 7.90/1.51      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | arAF0_sP0_0_1(X0)
% 7.90/1.51      | ~ iProver_ARSWP_102
% 7.90/1.51      | arAF0_r2_hidden_0 ),
% 7.90/1.51      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3311,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_102 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_2730]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5092,plain,
% 7.90/1.51      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_102 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4953,c_3311]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_13695,plain,
% 7.90/1.51      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_102 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5092,c_4672]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_14698,plain,
% 7.90/1.51      ( l1_pre_topc(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_102 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_13695,c_3971]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_20685,plain,
% 7.90/1.51      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_102 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_14698,c_4434]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9711,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5089,c_5091]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3874,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.90/1.51      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3875,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_3874]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_20236,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_9711,c_3875,c_4953]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5375,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4681,c_3316]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10312,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4288,c_5375]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_19008,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK5) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_10312,c_3746]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_19047,plain,
% 7.90/1.51      ( arAF0_sP0_0_1(sK5) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4953,c_19008]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_19498,plain,
% 7.90/1.51      ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_19047,c_4672]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6877,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_3310,c_4672]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9454,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | l1_pre_topc(X1) = iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6877,c_3971]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18869,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_sP1_0_1(X1) = iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_9454,c_4434]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9714,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8252,c_5091]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9987,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8252,c_9716]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4126,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X0))
% 7.90/1.51      | r1_tarski(arAF0_k3_subset_1_0,X0) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7914,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
% 7.90/1.51      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4126]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7915,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) != iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_7914]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8178,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
% 7.90/1.51      | ~ r1_tarski(arAF0_k4_xboole_0_0,arAF0_k4_xboole_0_0) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8179,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k4_xboole_0_0,arAF0_k4_xboole_0_0) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_8178]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9140,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8252,c_4953]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_290,plain,
% 7.90/1.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.90/1.51      theory(equality) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8132,plain,
% 7.90/1.51      ( m1_subset_1(X0,X1)
% 7.90/1.51      | ~ m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
% 7.90/1.51      | X1 != k1_zfmisc_1(arAF0_k4_xboole_0_0)
% 7.90/1.51      | X0 != arAF0_k4_xboole_0_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_290]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8431,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,X0)
% 7.90/1.51      | ~ m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
% 7.90/1.51      | X0 != k1_zfmisc_1(arAF0_k4_xboole_0_0)
% 7.90/1.51      | arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_8132]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10890,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
% 7.90/1.51      | ~ m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
% 7.90/1.51      | k1_zfmisc_1(arAF0_k4_xboole_0_0) != k1_zfmisc_1(arAF0_k4_xboole_0_0)
% 7.90/1.51      | arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_8431]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10891,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
% 7.90/1.51      | ~ m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0))
% 7.90/1.51      | arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0 ),
% 7.90/1.51      inference(equality_resolution_simp,[status(thm)],[c_10890]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10892,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 != arAF0_k4_xboole_0_0
% 7.90/1.51      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.51      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_10891]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16412,plain,
% 7.90/1.51      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_9987,c_7915,c_8179,c_8194,c_9140,c_10892]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16413,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(renaming,[status(thm)],[c_16412]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18664,plain,
% 7.90/1.51      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_9714,c_8179,c_8194,c_9140,c_10892]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18665,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(renaming,[status(thm)],[c_18664]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18676,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5089,c_18665]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18675,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8194,c_18665]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9712,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4173,c_5091]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4403,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.90/1.51      | ~ r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4404,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_4403]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5090,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4953,c_3316]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18608,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_9712,c_4404,c_5090]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18620,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6401,c_18608]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18154,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_18137,c_3316]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18409,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_18154,c_4953,c_5375]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18424,plain,
% 7.90/1.51      ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4288,c_18409]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18152,plain,
% 7.90/1.51      ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6402,c_18137]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_18057,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP1_0_1(X1) = iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_17078,c_4434]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3826,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_3660,c_3301]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4065,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_3826,c_3323]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6403,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5089,c_4065]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_26,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4246,plain,
% 7.90/1.51      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | ~ iProver_ARSWP_115
% 7.90/1.51      | arAF0_k3_subset_1_0 = arAF0_k2_struct_0_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_2743]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4247,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 = arAF0_k2_struct_0_0
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_4246]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3545,plain,
% 7.90/1.51      ( m1_subset_1(X0,X1)
% 7.90/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | X1 != k1_zfmisc_1(u1_struct_0(sK6))
% 7.90/1.51      | X0 != sK7 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_290]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4270,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,X0)
% 7.90/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | X0 != k1_zfmisc_1(u1_struct_0(sK6))
% 7.90/1.51      | arAF0_k3_subset_1_0 != sK7 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_3545]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4504,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 7.90/1.51      | arAF0_k3_subset_1_0 != sK7 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4270]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4505,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | arAF0_k3_subset_1_0 != sK7 ),
% 7.90/1.51      inference(equality_resolution_simp,[status(thm)],[c_4504]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4506,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 != sK7
% 7.90/1.51      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.90/1.51      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_4505]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4946,plain,
% 7.90/1.51      ( X0 = arAF0_k3_subset_1_0
% 7.90/1.51      | X0 != arAF0_k2_struct_0_0
% 7.90/1.51      | arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4055]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6366,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0
% 7.90/1.51      | arAF0_k2_struct_0_0 = arAF0_k3_subset_1_0
% 7.90/1.51      | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4946]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6367,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0
% 7.90/1.51      | arAF0_k2_struct_0_0 = arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(equality_resolution_simp,[status(thm)],[c_6366]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3639,plain,
% 7.90/1.51      ( m1_subset_1(X0,X1)
% 7.90/1.51      | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | X1 != k1_zfmisc_1(u1_struct_0(sK6))
% 7.90/1.51      | X0 != arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_290]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8466,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | m1_subset_1(arAF0_k2_struct_0_0,X0)
% 7.90/1.51      | X0 != k1_zfmisc_1(u1_struct_0(sK6))
% 7.90/1.51      | arAF0_k2_struct_0_0 != arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_3639]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_13006,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 7.90/1.51      | arAF0_k2_struct_0_0 != arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_8466]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_13007,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | arAF0_k2_struct_0_0 != arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(equality_resolution_simp,[status(thm)],[c_13006]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_13008,plain,
% 7.90/1.51      ( arAF0_k2_struct_0_0 != arAF0_k3_subset_1_0
% 7.90/1.51      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.90/1.51      | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_13007]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4915,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(X0))
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,X0) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_13252,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4915]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_13253,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) = iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_13252]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15050,plain,
% 7.90/1.51      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_6403,c_26,c_4172,c_4506,c_5089,c_6367,c_13008,c_13253]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15051,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(renaming,[status(thm)],[c_15050]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15060,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8252,c_15051]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3796,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3797,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_3796]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7648,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | m1_subset_1(arAF0_k4_xboole_0_0,X0)
% 7.90/1.51      | X0 != k1_zfmisc_1(u1_struct_0(sK6))
% 7.90/1.51      | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_3639]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_12985,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 7.90/1.51      | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_7648]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_12986,plain,
% 7.90/1.51      ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(equality_resolution_simp,[status(thm)],[c_12985]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_12987,plain,
% 7.90/1.51      ( arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0
% 7.90/1.51      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.90/1.51      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_12986]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_17540,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_15060,c_26,c_3797,c_4172,c_4506,c_5873,c_8194,c_12987]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_14,plain,
% 7.90/1.51      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.90/1.51      | ~ sP0(X1,X2)
% 7.90/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.90/1.51      | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
% 7.90/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_2734,plain,
% 7.90/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.90/1.51      | ~ arAF0_sP0_0_1(X1)
% 7.90/1.51      | ~ iProver_ARSWP_106
% 7.90/1.51      | ~ arAF0_r2_hidden_0
% 7.90/1.51      | arAF0_k9_subset_1_0 = X0 ),
% 7.90/1.51      inference(arg_filter_abstr,[status(unp)],[c_14]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3308,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = X0
% 7.90/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X1) != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_2734]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6489,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = X0
% 7.90/1.51      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X1) != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_3324,c_3308]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_17551,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_17540,c_6489]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_17924,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4783,c_17551]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_17308,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5089,c_17297]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9715,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6402,c_5091]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6081,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7))
% 7.90/1.51      | ~ r1_tarski(arAF0_k3_subset_1_0,sK7) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6082,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k3_subset_1_0,sK7) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_6081]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9988,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6402,c_9716]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7065,plain,
% 7.90/1.51      ( r1_tarski(X0,X1) | ~ r1_tarski(sK7,sK7) | X0 != sK7 | X1 != sK7 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_287]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7229,plain,
% 7.90/1.51      ( r1_tarski(X0,sK7) | ~ r1_tarski(sK7,sK7) | X0 != sK7 | sK7 != sK7 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_7065]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7230,plain,
% 7.90/1.51      ( r1_tarski(X0,sK7) | ~ r1_tarski(sK7,sK7) | X0 != sK7 ),
% 7.90/1.51      inference(equality_resolution_simp,[status(thm)],[c_7229]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7247,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,sK7)
% 7.90/1.51      | ~ r1_tarski(sK7,sK7)
% 7.90/1.51      | arAF0_k3_subset_1_0 != sK7 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_7230]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7248,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 != sK7
% 7.90/1.51      | r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
% 7.90/1.51      | r1_tarski(sK7,sK7) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_7247]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7307,plain,
% 7.90/1.51      ( r1_tarski(sK7,sK7) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6402,c_4953]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15193,plain,
% 7.90/1.51      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_9988,c_4172,c_7248,c_7307]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15194,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(renaming,[status(thm)],[c_15193]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16860,plain,
% 7.90/1.51      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_9715,c_4172,c_6082,c_7248,c_7307]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16861,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(renaming,[status(thm)],[c_16860]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16872,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4173,c_16861]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16871,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5089,c_16861]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16870,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8194,c_16861]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16424,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5089,c_16413]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6404,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5089,c_3826]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7504,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6404,c_3308]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15064,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_15051,c_6489]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16265,plain,
% 7.90/1.51      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_7504,c_4783,c_15064]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16266,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(renaming,[status(thm)],[c_16265]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9986,plain,
% 7.90/1.51      ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4172,c_9716]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3647,plain,
% 7.90/1.51      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_286]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3850,plain,
% 7.90/1.51      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_3647]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3851,plain,
% 7.90/1.51      ( X0 != sK7 | sK7 = X0 ),
% 7.90/1.51      inference(equality_resolution_simp,[status(thm)],[c_3850]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4268,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 != sK7 | sK7 = arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_3851]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4522,plain,
% 7.90/1.51      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.90/1.51      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | X0 != arAF0_k2_struct_0_0
% 7.90/1.51      | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_3873]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4523,plain,
% 7.90/1.51      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.90/1.51      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | X0 != arAF0_k2_struct_0_0 ),
% 7.90/1.51      inference(equality_resolution_simp,[status(thm)],[c_4522]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5489,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4523]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5490,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0
% 7.90/1.51      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_5489]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4107,plain,
% 7.90/1.51      ( r1_tarski(X0,X1)
% 7.90/1.51      | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | X0 != arAF0_k3_subset_1_0
% 7.90/1.51      | X1 != arAF0_k2_struct_0_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_287]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4879,plain,
% 7.90/1.51      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.90/1.51      | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | X0 != arAF0_k3_subset_1_0
% 7.90/1.51      | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4107]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4880,plain,
% 7.90/1.51      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.90/1.51      | ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | X0 != arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(equality_resolution_simp,[status(thm)],[c_4879]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6126,plain,
% 7.90/1.51      ( ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | r1_tarski(sK7,arAF0_k2_struct_0_0)
% 7.90/1.51      | sK7 != arAF0_k3_subset_1_0 ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4880]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6127,plain,
% 7.90/1.51      ( sK7 != arAF0_k3_subset_1_0
% 7.90/1.51      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_6126]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10702,plain,
% 7.90/1.51      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_9986,c_4172,c_4268,c_4953,c_5089,c_5490,c_6127]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10703,plain,
% 7.90/1.51      ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(renaming,[status(thm)],[c_10702]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15952,plain,
% 7.90/1.51      ( r1_tarski(sK7,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6401,c_10703]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9713,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4172,c_5091]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5242,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.90/1.51      | ~ r1_tarski(sK7,arAF0_k2_struct_0_0) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5243,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | r1_tarski(sK7,arAF0_k2_struct_0_0) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_5242]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_11011,plain,
% 7.90/1.51      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_9713,c_4172,c_4268,c_4953,c_5089,c_5243,c_5490,c_6127]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_11012,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(renaming,[status(thm)],[c_11011]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15950,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6401,c_11012]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15962,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6401,c_4953]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15530,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_14520,c_3746]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15204,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,sK7) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5089,c_15194]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_15203,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,sK7) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8194,c_15194]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_13292,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,sK7) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6402,c_5090]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8256,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8194,c_4065]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8551,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8256,c_6489]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_13081,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4783,c_8551]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6926,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6882,c_3300]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_12750,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4953,c_6926]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_17077,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | l1_pre_topc(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_7749,c_3300]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_16,plain,
% 7.90/1.51      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.90/1.51      | ~ sP0(X1,X2)
% 7.90/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.90/1.51      | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) ),
% 7.90/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_2736,plain,
% 7.90/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.90/1.51      | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.90/1.51      | ~ arAF0_sP0_0_1(X1)
% 7.90/1.51      | ~ iProver_ARSWP_108
% 7.90/1.51      | ~ arAF0_r2_hidden_0 ),
% 7.90/1.51      inference(arg_filter_abstr,[status(unp)],[c_16]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3307,plain,
% 7.90/1.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.90/1.51      | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X1) != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_2736]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5321,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_3321,c_3307]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5545,plain,
% 7.90/1.51      ( r1_tarski(arAF0_sK4_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5321,c_3323]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5564,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5545,c_3316]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5900,plain,
% 7.90/1.51      ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4288,c_5564]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3596,plain,
% 7.90/1.51      ( ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
% 7.90/1.51      inference(resolution,[status(thm)],[c_20,c_4]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3597,plain,
% 7.90/1.51      ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_3596]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5935,plain,
% 7.90/1.51      ( r1_tarski(sK7,u1_struct_0(sK5)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_5900]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_12003,plain,
% 7.90/1.51      ( arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_5900,c_3597,c_5935]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_12014,plain,
% 7.90/1.51      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4783,c_12003]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10348,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4172,c_5376]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_11280,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK5) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_10348,c_3322]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_11574,plain,
% 7.90/1.51      ( arAF0_sP0_0_1(sK5) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4953,c_11280]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_11644,plain,
% 7.90/1.51      ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_11574,c_4672]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_11277,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_10348,c_3323]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_11022,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6402,c_11012]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_11021,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k4_xboole_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8252,c_11012]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10712,plain,
% 7.90/1.51      ( r1_tarski(sK7,arAF0_k4_xboole_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8252,c_10703]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_10347,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_104 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4173,c_5376]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9983,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8194,c_9716]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9710,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_109 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8194,c_5091]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4291,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4173,c_3826]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3622,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.90/1.51      | ~ r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3623,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_3622]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5075,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_4291,c_3623,c_3904]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6493,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5075,c_3308]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_9492,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = arAF0_k4_xboole_0_0
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | iProver_ARSWP_97 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4783,c_6493]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8257,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8194,c_3826]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5565,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5545,c_3301]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8254,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8194,c_5565]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5948,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5565,c_3323]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8253,plain,
% 7.90/1.51      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8194,c_5948]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8255,plain,
% 7.90/1.51      ( arAF0_k4_xboole_0_0 = sK7
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_113 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_8194,c_4172]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_17080,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | l1_pre_topc(X1) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_7749,c_3301]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7753,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_103 != iProver_top
% 7.90/1.51      | iProver_ARSWP_98 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 = iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_6921,c_3301]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6494,plain,
% 7.90/1.51      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 7.90/1.51      | arAF0_sP0_0_1(X0) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5321,c_3308]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7131,plain,
% 7.90/1.51      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4783,c_6494]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7729,plain,
% 7.90/1.51      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,[status(thm)],[c_7131,c_4783]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6492,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_3826,c_3308]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_7282,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4783,c_6492]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6490,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = sK7
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_3321,c_3308]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6720,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 = sK7
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_106 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4783,c_6490]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5947,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4172,c_5565]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_27,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5996,plain,
% 7.90/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(instantiation,[status(thm)],[c_5947]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6138,plain,
% 7.90/1.51      ( arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(global_propositional_subsumption,
% 7.90/1.51                [status(thm)],
% 7.90/1.51                [c_5947,c_27,c_5996]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_6147,plain,
% 7.90/1.51      ( iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_114 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4783,c_6138]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5563,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 = arAF0_sK4_0
% 7.90/1.51      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_5545,c_3300]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5763,plain,
% 7.90/1.51      ( arAF0_k3_subset_1_0 = arAF0_sK4_0
% 7.90/1.51      | iProver_ARSWP_115 != iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | iProver_ARSWP_99 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_4783,c_5563]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_5320,plain,
% 7.90/1.51      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.90/1.51      | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X2) != iProver_top
% 7.90/1.51      | iProver_ARSWP_108 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_3324,c_3307]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3978,plain,
% 7.90/1.51      ( l1_pre_topc(sK6) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_3303,c_3971]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_4442,plain,
% 7.90/1.51      ( arAF0_sP1_0_1(sK6) = iProver_top
% 7.90/1.51      | iProver_ARSWP_112 != iProver_top
% 7.90/1.51      | iProver_ARSWP_111 != iProver_top
% 7.90/1.51      | iProver_ARSWP_110 != iProver_top ),
% 7.90/1.51      inference(superposition,[status(thm)],[c_3978,c_4434]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_8,plain,
% 7.90/1.51      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.90/1.51      | ~ r2_hidden(sK2(X2,X1),u1_pre_topc(X2))
% 7.90/1.51      | sP0(X2,X1)
% 7.90/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.90/1.51      | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
% 7.90/1.51      | k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)) != sK2(X2,X1) ),
% 7.90/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_2728,plain,
% 7.90/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.90/1.51      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.90/1.51      | arAF0_sP0_0_1(X2)
% 7.90/1.51      | ~ iProver_ARSWP_100
% 7.90/1.51      | ~ arAF0_r2_hidden_0
% 7.90/1.51      | arAF0_k9_subset_1_0 != arAF0_sK2_0 ),
% 7.90/1.51      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 7.90/1.51  
% 7.90/1.51  cnf(c_3313,plain,
% 7.90/1.51      ( arAF0_k9_subset_1_0 != arAF0_sK2_0
% 7.90/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.90/1.51      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.90/1.51      | arAF0_sP0_0_1(X2) = iProver_top
% 7.90/1.51      | iProver_ARSWP_100 != iProver_top
% 7.90/1.51      | arAF0_r2_hidden_0 != iProver_top ),
% 7.90/1.51      inference(predicate_to_equality,[status(thm)],[c_2728]) ).
% 7.90/1.51  
% 7.90/1.51  
% 7.90/1.51  % SZS output end Saturation for theBenchmark.p
% 7.90/1.51  
% 7.90/1.51  ------                               Statistics
% 7.90/1.51  
% 7.90/1.51  ------ Selected
% 7.90/1.51  
% 7.90/1.51  total_time:                             0.825
% 7.90/1.51  
%------------------------------------------------------------------------------
