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

% Result     : CounterSatisfiable 7.91s
% Output     : Saturation 7.91s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_9282)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f36,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_pre_topc(sK6,sK5)
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f20,f35,f34,f33])).

fof(f60,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
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

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f22,f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1)
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_289,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3428,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3430,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3769,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_3430])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_175,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_225,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_175])).

cnf(c_2832,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ iProver_ARSWP_117
    | arAF0_k3_subset_1_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_225])).

cnf(c_3407,plain,
    ( arAF0_k3_subset_1_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | iProver_ARSWP_117 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2832])).

cnf(c_8186,plain,
    ( arAF0_k3_subset_1_0 = sK7
    | iProver_ARSWP_117 != iProver_top ),
    inference(superposition,[status(thm)],[c_3769,c_3407])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_224,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_175])).

cnf(c_2831,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(X1))
    | ~ iProver_ARSWP_116 ),
    inference(arg_filter_abstr,[status(unp)],[c_224])).

cnf(c_3408,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(X1)) = iProver_top
    | iProver_ARSWP_116 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2831])).

cnf(c_3946,plain,
    ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_116 != iProver_top ),
    inference(superposition,[status(thm)],[c_3769,c_3408])).

cnf(c_4186,plain,
    ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_116 != iProver_top ),
    inference(superposition,[status(thm)],[c_3946,c_3430])).

cnf(c_8192,plain,
    ( arAF0_k7_subset_1_0 = arAF0_k3_subset_1_0
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top ),
    inference(superposition,[status(thm)],[c_4186,c_3407])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2819,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
    | arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_104
    | arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_3418,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2819])).

cnf(c_6623,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3418,c_3430])).

cnf(c_6983,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6623,c_3408])).

cnf(c_15355,plain,
    ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6983,c_3430])).

cnf(c_16365,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_15355])).

cnf(c_19390,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_16365])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3427,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2826,plain,
    ( arAF0_sP1_0_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ iProver_ARSWP_111 ),
    inference(arg_filter_abstr,[status(unp)],[c_19])).

cnf(c_3413,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_111 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2826])).

cnf(c_3795,plain,
    ( arAF0_sP1_0_1(X0)
    | ~ l1_pre_topc(X0)
    | ~ iProver_ARSWP_111 ),
    inference(resolution,[status(thm)],[c_2826,c_24])).

cnf(c_3796,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_111 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3795])).

cnf(c_4098,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_111 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3413,c_3796])).

cnf(c_4105,plain,
    ( arAF0_sP1_0_1(sK5) = iProver_top
    | iProver_ARSWP_111 != iProver_top ),
    inference(superposition,[status(thm)],[c_3427,c_4098])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2814,plain,
    ( arAF0_m1_pre_topc_0_1(X0)
    | ~ arAF0_sP0_0_1(X0)
    | ~ arAF0_sP1_0_1(X1)
    | ~ iProver_ARSWP_99 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_3423,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | arAF0_sP1_0_1(X1) != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2814])).

cnf(c_4677,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_4105,c_3423])).

cnf(c_19502,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_19390,c_4677])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2827,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_112 ),
    inference(arg_filter_abstr,[status(unp)],[c_20])).

cnf(c_3412,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2827])).

cnf(c_3881,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_112 ),
    inference(resolution,[status(thm)],[c_2827,c_24])).

cnf(c_3882,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3881])).

cnf(c_4013,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_112 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3412,c_3882])).

cnf(c_20061,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_19502,c_4013])).

cnf(c_24482,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_20061,c_4098])).

cnf(c_3431,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3429,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3857,plain,
    ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3431,c_3429])).

cnf(c_33581,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_24482,c_3857])).

cnf(c_6977,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6623,c_4677])).

cnf(c_7556,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6977,c_4013])).

cnf(c_17841,plain,
    ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7556,c_4098])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_223,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_175])).

cnf(c_2830,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1))
    | ~ iProver_ARSWP_115 ),
    inference(arg_filter_abstr,[status(unp)],[c_223])).

cnf(c_3409,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1)) = iProver_top
    | iProver_ARSWP_115 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2830])).

cnf(c_24984,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17841,c_3409])).

cnf(c_31938,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_24984])).

cnf(c_32893,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_31938,c_3429])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_175])).

cnf(c_2829,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ iProver_ARSWP_114
    | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_222])).

cnf(c_3410,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
    | r1_tarski(X0,X1) != iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2829])).

cnf(c_27,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2722,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2723,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2722])).

cnf(c_4622,plain,
    ( ~ r1_tarski(sK7,u1_struct_0(sK6))
    | ~ iProver_ARSWP_114
    | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_2829])).

cnf(c_4623,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
    | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4622])).

cnf(c_10052,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
    | iProver_ARSWP_114 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3410,c_27,c_2723,c_4623])).

cnf(c_31937,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_24984])).

cnf(c_17843,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7556,c_3409])).

cnf(c_31224,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_17843])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2828,negated_conjecture,
    ( arAF0_m1_pre_topc_0_1(sK6)
    | ~ iProver_ARSWP_113 ),
    inference(arg_filter_abstr,[status(unp)],[c_23])).

cnf(c_3411,plain,
    ( arAF0_m1_pre_topc_0_1(sK6) = iProver_top
    | iProver_ARSWP_113 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2828])).

cnf(c_8,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2815,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | arAF0_sP0_0_1(X0)
    | ~ arAF0_sP1_0_1(X1)
    | ~ iProver_ARSWP_100 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_3422,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | arAF0_sP1_0_1(X1) != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2815])).

cnf(c_4668,plain,
    ( arAF0_sP0_0_1(sK6) = iProver_top
    | arAF0_sP1_0_1(X0) != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_3411,c_3422])).

cnf(c_5015,plain,
    ( arAF0_sP0_0_1(sK6) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_4105,c_4668])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2825,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_110 ),
    inference(arg_filter_abstr,[status(unp)],[c_18])).

cnf(c_3414,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
    | arAF0_sP0_0_1(X0) != iProver_top
    | iProver_ARSWP_110 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_5117,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_3414])).

cnf(c_8187,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k2_struct_0_0
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_3407])).

cnf(c_13,plain,
    ( sP0(X0,X1)
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2820,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0)))
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_105 ),
    inference(arg_filter_abstr,[status(unp)],[c_13])).

cnf(c_3417,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2820])).

cnf(c_4856,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(arAF0_sK2_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_3430])).

cnf(c_4865,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_4856,c_3409])).

cnf(c_9742,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_3430])).

cnf(c_13377,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_9742])).

cnf(c_21255,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13377,c_5117])).

cnf(c_21270,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_21255,c_3409])).

cnf(c_26178,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21270,c_4865,c_5117])).

cnf(c_26179,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(renaming,[status(thm)],[c_26178])).

cnf(c_26197,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_26179,c_3430])).

cnf(c_26769,plain,
    ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_26197,c_3408])).

cnf(c_4866,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_4856,c_3408])).

cnf(c_29010,plain,
    ( iProver_ARSWP_116 != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26769,c_4866,c_5117])).

cnf(c_29011,plain,
    ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(renaming,[status(thm)],[c_29010])).

cnf(c_29024,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_29011])).

cnf(c_31041,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_29024])).

cnf(c_29026,plain,
    ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_29011,c_3430])).

cnf(c_30725,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_29026])).

cnf(c_30978,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_30725])).

cnf(c_6982,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6623,c_3409])).

cnf(c_14829,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6982,c_3430])).

cnf(c_15016,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_14829,c_4677])).

cnf(c_15992,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15016,c_4013])).

cnf(c_22769,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15992,c_4098])).

cnf(c_30154,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_22769])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_226,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_175])).

cnf(c_2833,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ iProver_ARSWP_118
    | arAF0_k7_subset_1_0 = arAF0_k4_xboole_0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_226])).

cnf(c_3406,plain,
    ( arAF0_k7_subset_1_0 = arAF0_k4_xboole_0_0
    | r1_tarski(X0,X1) != iProver_top
    | iProver_ARSWP_118 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2833])).

cnf(c_4406,plain,
    ( arAF0_k7_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_118 != iProver_top ),
    inference(superposition,[status(thm)],[c_3769,c_3406])).

cnf(c_29025,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_29011])).

cnf(c_29274,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_29025,c_3430])).

cnf(c_13379,plain,
    ( arAF0_k2_struct_0_0 = sK7
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_8186])).

cnf(c_13376,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k2_struct_0_0
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_10052])).

cnf(c_11484,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_4866])).

cnf(c_27339,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_11484])).

cnf(c_11483,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_4866])).

cnf(c_22190,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_11483])).

cnf(c_27730,plain,
    ( iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27339,c_5117,c_22190])).

cnf(c_27731,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(renaming,[status(thm)],[c_27730])).

cnf(c_27743,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_27731])).

cnf(c_28229,plain,
    ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_27743,c_3430])).

cnf(c_27744,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_27731,c_3430])).

cnf(c_5356,plain,
    ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_3408])).

cnf(c_13897,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_5356])).

cnf(c_4980,plain,
    ( ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4981,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4980])).

cnf(c_13900,plain,
    ( r1_tarski(arAF0_k7_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_5356,c_3430])).

cnf(c_13966,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_13900])).

cnf(c_4057,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
    | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4058,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4057])).

cnf(c_4285,plain,
    ( ~ r1_tarski(sK7,u1_struct_0(sK6))
    | ~ iProver_ARSWP_117
    | arAF0_k3_subset_1_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_2832])).

cnf(c_4286,plain,
    ( arAF0_k3_subset_1_0 = sK7
    | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top
    | iProver_ARSWP_117 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4285])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3834,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_6586,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | X1 != k1_zfmisc_1(arAF0_k2_struct_0_0)
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3834])).

cnf(c_8461,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | X0 != sK7
    | k1_zfmisc_1(arAF0_k2_struct_0_0) != k1_zfmisc_1(arAF0_k2_struct_0_0) ),
    inference(instantiation,[status(thm)],[c_6586])).

cnf(c_8462,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | X0 != sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_8461])).

cnf(c_8497,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_8462])).

cnf(c_8498,plain,
    ( arAF0_k3_subset_1_0 != sK7
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8497])).

cnf(c_5355,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_3409])).

cnf(c_8554,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_5355])).

cnf(c_7299,plain,
    ( ~ r1_tarski(sK7,arAF0_k2_struct_0_0)
    | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7300,plain,
    ( r1_tarski(sK7,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7299])).

cnf(c_5408,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_5355,c_3430])).

cnf(c_8551,plain,
    ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_5408])).

cnf(c_303,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3760,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_4067,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3760])).

cnf(c_4068,plain,
    ( X0 != sK7
    | sK7 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4067])).

cnf(c_4328,plain,
    ( arAF0_k3_subset_1_0 != sK7
    | sK7 = arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_4068])).

cnf(c_307,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3930,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k2_struct_0_0
    | X1 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_4532,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k2_struct_0_0
    | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_3930])).

cnf(c_4533,plain,
    ( r1_tarski(X0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | X0 != arAF0_k2_struct_0_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4532])).

cnf(c_5001,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
    | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0 ),
    inference(instantiation,[status(thm)],[c_4533])).

cnf(c_5002,plain,
    ( arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5001])).

cnf(c_4060,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | X1 != k1_zfmisc_1(arAF0_k2_struct_0_0)
    | X0 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_6312,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | X0 != arAF0_k3_subset_1_0
    | k1_zfmisc_1(arAF0_k2_struct_0_0) != k1_zfmisc_1(arAF0_k2_struct_0_0) ),
    inference(instantiation,[status(thm)],[c_4060])).

cnf(c_6313,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | X0 != arAF0_k3_subset_1_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6312])).

cnf(c_6493,plain,
    ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
    | sK7 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_6313])).

cnf(c_6494,plain,
    ( sK7 != arAF0_k3_subset_1_0
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6493])).

cnf(c_3826,plain,
    ( r1_tarski(sK7,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6583,plain,
    ( r1_tarski(sK7,arAF0_k2_struct_0_0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) ),
    inference(instantiation,[status(thm)],[c_3826])).

cnf(c_6584,plain,
    ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6583])).

cnf(c_9141,plain,
    ( iProver_ARSWP_117 != iProver_top
    | r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8551,c_27,c_2723,c_4286,c_4328,c_4981,c_5002,c_5117,c_6494,c_6584,c_8187])).

cnf(c_9142,plain,
    ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(renaming,[status(thm)],[c_9141])).

cnf(c_9364,plain,
    ( iProver_ARSWP_117 != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8554,c_27,c_2723,c_4286,c_4328,c_5002,c_5117,c_7300,c_8187,c_9282])).

cnf(c_9365,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(renaming,[status(thm)],[c_9364])).

cnf(c_18264,plain,
    ( iProver_ARSWP_117 != iProver_top
    | r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13966,c_5002,c_5117,c_8187])).

cnf(c_18265,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(renaming,[status(thm)],[c_18264])).

cnf(c_22390,plain,
    ( iProver_ARSWP_117 != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13897,c_4981,c_5002,c_5117,c_8187])).

cnf(c_22391,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(renaming,[status(thm)],[c_22390])).

cnf(c_22401,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_22391])).

cnf(c_3931,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3932,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3931])).

cnf(c_27050,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22401,c_3932,c_5117])).

cnf(c_26765,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_26197])).

cnf(c_26195,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_26179])).

cnf(c_24983,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17841,c_3407])).

cnf(c_26125,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_24983])).

cnf(c_13378,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_4865])).

cnf(c_25924,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13378,c_5117])).

cnf(c_25937,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_25924])).

cnf(c_19519,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_19390,c_3857])).

cnf(c_19716,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_19519])).

cnf(c_20006,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_19716,c_4677])).

cnf(c_20279,plain,
    ( l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_20006,c_4013])).

cnf(c_25496,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_20279,c_4098])).

cnf(c_15014,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_14829])).

cnf(c_15532,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15014,c_3857])).

cnf(c_15567,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_15532])).

cnf(c_16132,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15567,c_4677])).

cnf(c_18323,plain,
    ( l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_16132,c_4013])).

cnf(c_25358,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_18323,c_4098])).

cnf(c_24985,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17841,c_3408])).

cnf(c_15341,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_6983])).

cnf(c_15785,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15341,c_4677])).

cnf(c_17751,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15785,c_4013])).

cnf(c_24764,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17751,c_4098])).

cnf(c_24488,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_20061,c_3857])).

cnf(c_15797,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15341,c_3430])).

cnf(c_16596,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15797,c_4677])).

cnf(c_17509,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_16596,c_4013])).

cnf(c_24340,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17509,c_4098])).

cnf(c_15515,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15014,c_4677])).

cnf(c_16311,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15515,c_4013])).

cnf(c_23833,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_16311,c_3857])).

cnf(c_8190,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK2_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_4856,c_3407])).

cnf(c_12187,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK2_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_8190])).

cnf(c_20852,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK2_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_12187,c_4677])).

cnf(c_21504,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK2_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_20852,c_4013])).

cnf(c_23679,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK2_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_21504,c_4098])).

cnf(c_8188,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6977,c_3407])).

cnf(c_21550,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_8188])).

cnf(c_23613,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_21550,c_4013])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2817,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_102
    | arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 = arAF0_sK2_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_3420,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_102 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2817])).

cnf(c_5747,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_3420])).

cnf(c_19126,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5747,c_4677])).

cnf(c_19792,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_19126,c_4013])).

cnf(c_23186,plain,
    ( arAF0_k9_subset_1_0 = arAF0_sK2_0
    | arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_102 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_19792,c_4098])).

cnf(c_16368,plain,
    ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15355,c_4677])).

cnf(c_17410,plain,
    ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_16368,c_4013])).

cnf(c_23096,plain,
    ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_17410,c_4098])).

cnf(c_15989,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_15016])).

cnf(c_22665,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15989,c_4013])).

cnf(c_22403,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_22391])).

cnf(c_22193,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_11483])).

cnf(c_22192,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_11483])).

cnf(c_11,plain,
    ( r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
    | sP0(X0,X1)
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2818,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | arAF0_sP0_0_1(X0)
    | ~ iProver_ARSWP_103
    | arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_3419,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_103 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2818])).

cnf(c_5357,plain,
    ( arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_3419])).

cnf(c_15295,plain,
    ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5357,c_4677])).

cnf(c_15745,plain,
    ( l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15295,c_4013])).

cnf(c_21940,plain,
    ( arAF0_sP1_0_1(X0) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_103 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15745,c_4098])).

cnf(c_4555,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_115 != iProver_top ),
    inference(superposition,[status(thm)],[c_3769,c_3409])).

cnf(c_5039,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_115 != iProver_top ),
    inference(superposition,[status(thm)],[c_4555,c_3430])).

cnf(c_10066,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_5039])).

cnf(c_10430,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(superposition,[status(thm)],[c_10066,c_3407])).

cnf(c_4658,plain,
    ( X0 != X1
    | arAF0_k3_subset_1_0 != X1
    | arAF0_k3_subset_1_0 = X0 ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_5199,plain,
    ( X0 != arAF0_k3_subset_1_0
    | arAF0_k3_subset_1_0 = X0
    | arAF0_k3_subset_1_0 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_4658])).

cnf(c_5200,plain,
    ( X0 != arAF0_k3_subset_1_0
    | arAF0_k3_subset_1_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5199])).

cnf(c_6737,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
    | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_5200])).

cnf(c_21350,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_114 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10430,c_27,c_2723,c_4623,c_6737])).

cnf(c_21268,plain,
    ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_21255])).

cnf(c_6618,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_3418,c_4677])).

cnf(c_7633,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6618,c_4013])).

cnf(c_21022,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP1_0_1(X1) = iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7633,c_4098])).

cnf(c_9384,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_3946])).

cnf(c_3660,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK6))
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_4330,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK6))
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3660])).

cnf(c_4767,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_4330])).

cnf(c_4768,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_4767])).

cnf(c_4769,plain,
    ( arAF0_k3_subset_1_0 != sK7
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4768])).

cnf(c_10658,plain,
    ( iProver_ARSWP_117 != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9384,c_27,c_2723,c_4286,c_4769])).

cnf(c_10659,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_117 != iProver_top ),
    inference(renaming,[status(thm)],[c_10658])).

cnf(c_13374,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_10659])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2822,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_107
    | ~ arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_15])).

cnf(c_3416,plain,
    ( arAF0_k9_subset_1_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2822])).

cnf(c_18489,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_13374,c_3416])).

cnf(c_20472,plain,
    ( arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18489,c_5015])).

cnf(c_20067,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_19502,c_3857])).

cnf(c_7557,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6977,c_3409])).

cnf(c_18923,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_7557])).

cnf(c_13591,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_5355])).

cnf(c_9700,plain,
    ( ~ r1_tarski(arAF0_k3_subset_1_0,sK7)
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_9701,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,sK7) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9700])).

cnf(c_13588,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_5408])).

cnf(c_4363,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,X0)
    | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9322,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,sK7)
    | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_4363])).

cnf(c_9323,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9322])).

cnf(c_9265,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
    | X1 != k1_zfmisc_1(sK7)
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3834])).

cnf(c_11390,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
    | X0 != k1_zfmisc_1(sK7)
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_9265])).

cnf(c_13316,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
    | k1_zfmisc_1(sK7) != k1_zfmisc_1(sK7)
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_11390])).

cnf(c_13317,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_13316])).

cnf(c_13318,plain,
    ( arAF0_k3_subset_1_0 != sK7
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13317])).

cnf(c_13586,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_9365])).

cnf(c_18103,plain,
    ( iProver_ARSWP_117 != iProver_top
    | r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13588,c_27,c_2723,c_4286,c_9323,c_13318,c_13586])).

cnf(c_18104,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(renaming,[status(thm)],[c_18103])).

cnf(c_18726,plain,
    ( iProver_ARSWP_117 != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13591,c_27,c_2723,c_4286,c_13318,c_13586])).

cnf(c_18727,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(renaming,[status(thm)],[c_18726])).

cnf(c_18738,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_18727])).

cnf(c_18736,plain,
    ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_18727])).

cnf(c_18276,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_18265])).

cnf(c_18115,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,sK7) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_18104])).

cnf(c_18113,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,sK7) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_18104])).

cnf(c_11485,plain,
    ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_4866,c_3430])).

cnf(c_11930,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_11485])).

cnf(c_16889,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_11930])).

cnf(c_17073,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_16889,c_3857])).

cnf(c_17097,plain,
    ( arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_17073])).

cnf(c_17239,plain,
    ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_17097,c_4677])).

cnf(c_16888,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_11930])).

cnf(c_16317,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_m1_pre_topc_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_15515,c_3857])).

cnf(c_15013,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_14829])).

cnf(c_14814,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X1) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_6982])).

cnf(c_13898,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_5356])).

cnf(c_14571,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_13898])).

cnf(c_13967,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_13900])).

cnf(c_14461,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,sK7) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_13967])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ sP0(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2824,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ arAF0_sP0_0_1(X1)
    | ~ iProver_ARSWP_109
    | ~ arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_17])).

cnf(c_3415,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2824])).

cnf(c_5522,plain,
    ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_3415])).

cnf(c_5588,plain,
    ( r1_tarski(arAF0_sK4_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5522,c_3430])).

cnf(c_5714,plain,
    ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5588,c_3408])).

cnf(c_6410,plain,
    ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5714,c_3430])).

cnf(c_9380,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_6410])).

cnf(c_14262,plain,
    ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_9380])).

cnf(c_3711,plain,
    ( ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_21,c_5])).

cnf(c_3712,plain,
    ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3711])).

cnf(c_14356,plain,
    ( r1_tarski(sK7,u1_struct_0(sK5)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(instantiation,[status(thm)],[c_14262])).

cnf(c_14359,plain,
    ( arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14262,c_3712,c_14356])).

cnf(c_14370,plain,
    ( iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_14359])).

cnf(c_10664,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_10659])).

cnf(c_12788,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_10664,c_3416])).

cnf(c_14211,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_12788])).

cnf(c_5889,plain,
    ( arAF0_k9_subset_1_0 = X0
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3431,c_3416])).

cnf(c_10434,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_10066,c_5889])).

cnf(c_14184,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_10434])).

cnf(c_13968,plain,
    ( r1_tarski(arAF0_k7_subset_1_0,sK7) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_13900])).

cnf(c_13899,plain,
    ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_5356])).

cnf(c_13592,plain,
    ( r1_tarski(sK7,sK7) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_5117])).

cnf(c_9383,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_4186])).

cnf(c_3688,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK7,u1_struct_0(sK6))
    | X1 != u1_struct_0(sK6)
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_4329,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,X0)
    | ~ r1_tarski(sK7,u1_struct_0(sK6))
    | X0 != u1_struct_0(sK6)
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3688])).

cnf(c_4373,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6))
    | ~ r1_tarski(sK7,u1_struct_0(sK6))
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_4329])).

cnf(c_4374,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6))
    | ~ r1_tarski(sK7,u1_struct_0(sK6))
    | arAF0_k3_subset_1_0 != sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_4373])).

cnf(c_4375,plain,
    ( arAF0_k3_subset_1_0 != sK7
    | r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top
    | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4374])).

cnf(c_10180,plain,
    ( iProver_ARSWP_117 != iProver_top
    | r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9383,c_27,c_2723,c_4286,c_4375])).

cnf(c_10181,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_117 != iProver_top ),
    inference(renaming,[status(thm)],[c_10180])).

cnf(c_13375,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_10181])).

cnf(c_4426,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_4186])).

cnf(c_8195,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top ),
    inference(superposition,[status(thm)],[c_4426,c_3407])).

cnf(c_13373,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k2_struct_0_0
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_8187,c_8195])).

cnf(c_13019,plain,
    ( arAF0_k4_xboole_0_0 = sK7
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top ),
    inference(superposition,[status(thm)],[c_8195,c_8186])).

cnf(c_13129,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_13019,c_11484])).

cnf(c_17842,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7556,c_3407])).

cnf(c_8189,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6623,c_3407])).

cnf(c_12198,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK3_0
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_8189])).

cnf(c_10192,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_10181,c_5889])).

cnf(c_11987,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_10192])).

cnf(c_11931,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_11485])).

cnf(c_9779,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_9742])).

cnf(c_10878,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_9779,c_3857])).

cnf(c_10925,plain,
    ( arAF0_sP0_0_1(sK5) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_10878])).

cnf(c_11102,plain,
    ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_105 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | iProver_ARSWP_99 != iProver_top ),
    inference(superposition,[status(thm)],[c_10925,c_4677])).

cnf(c_10186,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_10181])).

cnf(c_10067,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_4555])).

cnf(c_10065,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_5355])).

cnf(c_5713,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5588,c_3409])).

cnf(c_10064,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_5713])).

cnf(c_6374,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5713,c_3430])).

cnf(c_10063,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_6374])).

cnf(c_10062,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_110 != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_5408])).

cnf(c_10060,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_4865])).

cnf(c_10059,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_114 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_9742])).

cnf(c_10061,plain,
    ( arAF0_k4_xboole_0_0 = sK7
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_114 != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_8186])).

cnf(c_9741,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(X0) = iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_4865])).

cnf(c_8552,plain,
    ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_6374])).

cnf(c_28,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8553,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8186,c_5713])).

cnf(c_8614,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(instantiation,[status(thm)],[c_8553])).

cnf(c_8861,plain,
    ( arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8552,c_28,c_8614])).

cnf(c_8872,plain,
    ( iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_8861])).

cnf(c_8196,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK4_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5588,c_3407])).

cnf(c_8625,plain,
    ( arAF0_k3_subset_1_0 = arAF0_sK4_0
    | iProver_ARSWP_117 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_8196])).

cnf(c_17844,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X1) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_7556,c_3408])).

cnf(c_4427,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_3946])).

cnf(c_5895,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4427,c_3416])).

cnf(c_7771,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_5895])).

cnf(c_7558,plain,
    ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_m1_pre_topc_0_1(X1) = iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_104 != iProver_top
    | iProver_ARSWP_99 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_6977,c_3408])).

cnf(c_5892,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(X0) != iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5522,c_3416])).

cnf(c_6109,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_5892])).

cnf(c_7384,plain,
    ( arAF0_sK4_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6109,c_5015])).

cnf(c_6945,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_6410])).

cnf(c_6409,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_118 != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_5714])).

cnf(c_5894,plain,
    ( arAF0_k7_subset_1_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3946,c_3416])).

cnf(c_6223,plain,
    ( arAF0_k7_subset_1_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_116 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_5894])).

cnf(c_5893,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_4555,c_3416])).

cnf(c_6215,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_5893])).

cnf(c_5890,plain,
    ( arAF0_k9_subset_1_0 = sK7
    | arAF0_sP0_0_1(sK6) != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_3416])).

cnf(c_5973,plain,
    ( arAF0_k9_subset_1_0 = sK7
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_111 != iProver_top
    | iProver_ARSWP_107 != iProver_top
    | iProver_ARSWP_100 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_5890])).

cnf(c_5521,plain,
    ( r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | arAF0_sP0_0_1(X1) != iProver_top
    | iProver_ARSWP_109 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_3431,c_3415])).

cnf(c_4020,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top ),
    inference(superposition,[status(thm)],[c_3411,c_4013])).

cnf(c_4181,plain,
    ( arAF0_sP1_0_1(sK6) = iProver_top
    | iProver_ARSWP_113 != iProver_top
    | iProver_ARSWP_112 != iProver_top
    | iProver_ARSWP_111 != iProver_top ),
    inference(superposition,[status(thm)],[c_4020,c_4098])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(sK2(X2,X1),u1_pre_topc(X2))
    | sP0(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)) != sK2(X2,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2816,plain,
    ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | arAF0_sP0_0_1(X2)
    | ~ iProver_ARSWP_101
    | ~ arAF0_r2_hidden_0
    | arAF0_k9_subset_1_0 != arAF0_sK2_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_3421,plain,
    ( arAF0_k9_subset_1_0 != arAF0_sK2_0
    | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | arAF0_sP0_0_1(X2) = iProver_top
    | iProver_ARSWP_101 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2816])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.91/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/1.48  
% 7.91/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.91/1.48  
% 7.91/1.48  ------  iProver source info
% 7.91/1.48  
% 7.91/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.91/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.91/1.48  git: non_committed_changes: false
% 7.91/1.48  git: last_make_outside_of_git: false
% 7.91/1.48  
% 7.91/1.48  ------ 
% 7.91/1.48  ------ Parsing...
% 7.91/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.48  ------ Proving...
% 7.91/1.48  ------ Problem Properties 
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  clauses                                 25
% 7.91/1.48  conjectures                             4
% 7.91/1.48  EPR                                     6
% 7.91/1.48  Horn                                    21
% 7.91/1.48  unary                                   4
% 7.91/1.48  binary                                  8
% 7.91/1.48  lits                                    70
% 7.91/1.48  lits eq                                 6
% 7.91/1.48  fd_pure                                 0
% 7.91/1.48  fd_pseudo                               0
% 7.91/1.48  fd_cond                                 0
% 7.91/1.48  fd_pseudo_cond                          0
% 7.91/1.48  AC symbols                              0
% 7.91/1.48  
% 7.91/1.48  ------ Input Options Time Limit: Unbounded
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing...
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.91/1.48  Current options:
% 7.91/1.48  ------ 
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Proving...
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing...
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing...
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing...
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.48  
% 7.91/1.48  ------ Proving...
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.48  
% 7.91/1.48  ------ Proving...
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.48  
% 7.91/1.48  ------ Proving...
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.48  
% 7.91/1.48  ------ Proving...
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.48  
% 7.91/1.48  ------ Proving...
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.48  
% 7.91/1.48  ------ Proving...
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.91/1.48  
% 7.91/1.48  ------ Proving...
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.48  
% 7.91/1.48  ------ Proving...
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  % SZS status CounterSatisfiable for theBenchmark.p
% 7.91/1.48  
% 7.91/1.48  % SZS output start Saturation for theBenchmark.p
% 7.91/1.48  
% 7.91/1.48  fof(f10,conjecture,(
% 7.91/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.91/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f11,negated_conjecture,(
% 7.91/1.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.91/1.48    inference(negated_conjecture,[],[f10])).
% 7.91/1.48  
% 7.91/1.48  fof(f20,plain,(
% 7.91/1.48    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 7.91/1.48    inference(ennf_transformation,[],[f11])).
% 7.91/1.48  
% 7.91/1.48  fof(f35,plain,(
% 7.91/1.48    ( ! [X0,X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.91/1.48    introduced(choice_axiom,[])).
% 7.91/1.48  
% 7.91/1.48  fof(f34,plain,(
% 7.91/1.48    ( ! [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) => (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_pre_topc(sK6,X0))) )),
% 7.91/1.48    introduced(choice_axiom,[])).
% 7.91/1.48  
% 7.91/1.48  fof(f33,plain,(
% 7.91/1.48    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X1,sK5)) & l1_pre_topc(sK5))),
% 7.91/1.48    introduced(choice_axiom,[])).
% 7.91/1.48  
% 7.91/1.48  fof(f36,plain,(
% 7.91/1.48    ((~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_pre_topc(sK6,sK5)) & l1_pre_topc(sK5)),
% 7.91/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f20,f35,f34,f33])).
% 7.91/1.48  
% 7.91/1.48  fof(f60,plain,(
% 7.91/1.48    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 7.91/1.48    inference(cnf_transformation,[],[f36])).
% 7.91/1.48  
% 7.91/1.48  fof(f6,axiom,(
% 7.91/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.91/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f24,plain,(
% 7.91/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.91/1.48    inference(nnf_transformation,[],[f6])).
% 7.91/1.48  
% 7.91/1.48  fof(f42,plain,(
% 7.91/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.91/1.48    inference(cnf_transformation,[],[f24])).
% 7.91/1.48  
% 7.91/1.48  fof(f4,axiom,(
% 7.91/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.91/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f16,plain,(
% 7.91/1.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.91/1.48    inference(ennf_transformation,[],[f4])).
% 7.91/1.48  
% 7.91/1.48  fof(f40,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.91/1.48    inference(cnf_transformation,[],[f16])).
% 7.91/1.48  
% 7.91/1.48  fof(f43,plain,(
% 7.91/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f24])).
% 7.91/1.48  
% 7.91/1.48  fof(f3,axiom,(
% 7.91/1.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.91/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f15,plain,(
% 7.91/1.48    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.91/1.48    inference(ennf_transformation,[],[f3])).
% 7.91/1.48  
% 7.91/1.48  fof(f39,plain,(
% 7.91/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.91/1.48    inference(cnf_transformation,[],[f15])).
% 7.91/1.48  
% 7.91/1.48  fof(f21,plain,(
% 7.91/1.48    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 7.91/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.91/1.48  
% 7.91/1.48  fof(f26,plain,(
% 7.91/1.48    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.91/1.48    inference(nnf_transformation,[],[f21])).
% 7.91/1.48  
% 7.91/1.48  fof(f27,plain,(
% 7.91/1.48    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.91/1.48    inference(flattening,[],[f26])).
% 7.91/1.48  
% 7.91/1.48  fof(f28,plain,(
% 7.91/1.48    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.91/1.48    inference(rectify,[],[f27])).
% 7.91/1.48  
% 7.91/1.48  fof(f31,plain,(
% 7.91/1.48    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.91/1.48    introduced(choice_axiom,[])).
% 7.91/1.48  
% 7.91/1.48  fof(f30,plain,(
% 7.91/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 7.91/1.48    introduced(choice_axiom,[])).
% 7.91/1.48  
% 7.91/1.48  fof(f29,plain,(
% 7.91/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.91/1.48    introduced(choice_axiom,[])).
% 7.91/1.48  
% 7.91/1.48  fof(f32,plain,(
% 7.91/1.48    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.91/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).
% 7.91/1.48  
% 7.91/1.48  fof(f52,plain,(
% 7.91/1.48    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.91/1.48    inference(cnf_transformation,[],[f32])).
% 7.91/1.48  
% 7.91/1.48  fof(f58,plain,(
% 7.91/1.48    l1_pre_topc(sK5)),
% 7.91/1.48    inference(cnf_transformation,[],[f36])).
% 7.91/1.48  
% 7.91/1.48  fof(f7,axiom,(
% 7.91/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 7.91/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f18,plain,(
% 7.91/1.48    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.91/1.48    inference(ennf_transformation,[],[f7])).
% 7.91/1.48  
% 7.91/1.48  fof(f22,plain,(
% 7.91/1.48    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 7.91/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.91/1.48  
% 7.91/1.48  fof(f23,plain,(
% 7.91/1.48    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.91/1.48    inference(definition_folding,[],[f18,f22,f21])).
% 7.91/1.48  
% 7.91/1.48  fof(f56,plain,(
% 7.91/1.48    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f23])).
% 7.91/1.48  
% 7.91/1.48  fof(f25,plain,(
% 7.91/1.48    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 7.91/1.48    inference(nnf_transformation,[],[f22])).
% 7.91/1.48  
% 7.91/1.48  fof(f45,plain,(
% 7.91/1.48    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f25])).
% 7.91/1.48  
% 7.91/1.48  fof(f9,axiom,(
% 7.91/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.91/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f19,plain,(
% 7.91/1.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.91/1.48    inference(ennf_transformation,[],[f9])).
% 7.91/1.48  
% 7.91/1.48  fof(f57,plain,(
% 7.91/1.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f19])).
% 7.91/1.48  
% 7.91/1.48  fof(f61,plain,(
% 7.91/1.48    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))),
% 7.91/1.48    inference(cnf_transformation,[],[f36])).
% 7.91/1.48  
% 7.91/1.48  fof(f2,axiom,(
% 7.91/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.91/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f14,plain,(
% 7.91/1.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.91/1.48    inference(ennf_transformation,[],[f2])).
% 7.91/1.48  
% 7.91/1.48  fof(f38,plain,(
% 7.91/1.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.91/1.48    inference(cnf_transformation,[],[f14])).
% 7.91/1.48  
% 7.91/1.48  fof(f1,axiom,(
% 7.91/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 7.91/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f13,plain,(
% 7.91/1.48    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.91/1.48    inference(ennf_transformation,[],[f1])).
% 7.91/1.48  
% 7.91/1.48  fof(f37,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.91/1.48    inference(cnf_transformation,[],[f13])).
% 7.91/1.48  
% 7.91/1.48  fof(f59,plain,(
% 7.91/1.48    m1_pre_topc(sK6,sK5)),
% 7.91/1.48    inference(cnf_transformation,[],[f36])).
% 7.91/1.48  
% 7.91/1.48  fof(f44,plain,(
% 7.91/1.48    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f25])).
% 7.91/1.48  
% 7.91/1.48  fof(f46,plain,(
% 7.91/1.48    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f32])).
% 7.91/1.48  
% 7.91/1.48  fof(f51,plain,(
% 7.91/1.48    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.91/1.48    inference(cnf_transformation,[],[f32])).
% 7.91/1.49  
% 7.91/1.49  fof(f5,axiom,(
% 7.91/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.91/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f17,plain,(
% 7.91/1.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.91/1.49    inference(ennf_transformation,[],[f5])).
% 7.91/1.49  
% 7.91/1.49  fof(f41,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f17])).
% 7.91/1.49  
% 7.91/1.49  fof(f54,plain,(
% 7.91/1.49    ( ! [X0,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f32])).
% 7.91/1.49  
% 7.91/1.49  fof(f53,plain,(
% 7.91/1.49    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f32])).
% 7.91/1.49  
% 7.91/1.49  fof(f49,plain,(
% 7.91/1.49    ( ! [X0,X5,X1] : (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f32])).
% 7.91/1.49  
% 7.91/1.49  fof(f47,plain,(
% 7.91/1.49    ( ! [X0,X5,X1] : (m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f32])).
% 7.91/1.49  
% 7.91/1.49  fof(f55,plain,(
% 7.91/1.49    ( ! [X0,X3,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f32])).
% 7.91/1.49  
% 7.91/1.49  cnf(c_289,plain,( X0_2 = X0_2 ),theory(equality) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22,negated_conjecture,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3428,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6,plain,
% 7.91/1.49      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3430,plain,
% 7.91/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.91/1.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3769,plain,
% 7.91/1.49      ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3428,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.91/1.49      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_175,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.91/1.49      inference(prop_impl,[status(thm)],[c_5]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_225,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.91/1.49      inference(bin_hyper_res,[status(thm)],[c_3,c_175]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2832,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1) | ~ iProver_ARSWP_117 | arAF0_k3_subset_1_0 = X0 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_225]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3407,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = X0
% 7.91/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2832]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8186,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = sK7 | iProver_ARSWP_117 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3769,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.91/1.49      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_224,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1)
% 7.91/1.49      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 7.91/1.49      inference(bin_hyper_res,[status(thm)],[c_2,c_175]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2831,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1)
% 7.91/1.49      | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(X1))
% 7.91/1.49      | ~ iProver_ARSWP_116 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_224]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3408,plain,
% 7.91/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(X1)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2831]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3946,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3769,c_3408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4186,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(sK6)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3946,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8192,plain,
% 7.91/1.49      ( arAF0_k7_subset_1_0 = arAF0_k3_subset_1_0
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4186,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12,plain,
% 7.91/1.49      ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 7.91/1.49      | sP0(X0,X1)
% 7.91/1.49      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
% 7.91/1.49      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2819,plain,
% 7.91/1.49      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0)))
% 7.91/1.49      | arAF0_sP0_0_1(X1)
% 7.91/1.49      | ~ iProver_ARSWP_104
% 7.91/1.49      | arAF0_r2_hidden_0 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3418,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2819]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6623,plain,
% 7.91/1.49      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3418,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6983,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6623,c_3408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15355,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6983,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_16365,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8192,c_15355]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_19390,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_16365]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_24,negated_conjecture,
% 7.91/1.49      ( l1_pre_topc(sK5) ),
% 7.91/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3427,plain,
% 7.91/1.49      ( l1_pre_topc(sK5) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_19,plain,
% 7.91/1.49      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 7.91/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2826,plain,
% 7.91/1.49      ( arAF0_sP1_0_1(X0)
% 7.91/1.49      | ~ l1_pre_topc(X1)
% 7.91/1.49      | ~ l1_pre_topc(X0)
% 7.91/1.49      | ~ iProver_ARSWP_111 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_19]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3413,plain,
% 7.91/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | l1_pre_topc(X1) != iProver_top
% 7.91/1.49      | l1_pre_topc(X0) != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2826]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3795,plain,
% 7.91/1.49      ( arAF0_sP1_0_1(X0) | ~ l1_pre_topc(X0) | ~ iProver_ARSWP_111 ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_2826,c_24]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3796,plain,
% 7.91/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | l1_pre_topc(X0) != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_3795]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4098,plain,
% 7.91/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | l1_pre_topc(X0) != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3413,c_3796]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4105,plain,
% 7.91/1.49      ( arAF0_sP1_0_1(sK5) = iProver_top | iProver_ARSWP_111 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3427,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7,plain,
% 7.91/1.49      ( ~ sP1(X0,X1) | ~ sP0(X1,X0) | m1_pre_topc(X1,X0) ),
% 7.91/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2814,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(X0)
% 7.91/1.49      | ~ arAF0_sP0_0_1(X0)
% 7.91/1.49      | ~ arAF0_sP1_0_1(X1)
% 7.91/1.49      | ~ iProver_ARSWP_99 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3423,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) != iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2814]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4677,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4105,c_3423]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_19502,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_19390,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_20,plain,
% 7.91/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.91/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2827,plain,
% 7.91/1.49      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 7.91/1.49      | ~ l1_pre_topc(X1)
% 7.91/1.49      | l1_pre_topc(X0)
% 7.91/1.49      | ~ iProver_ARSWP_112 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_20]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3412,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X1) != iProver_top
% 7.91/1.49      | l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2827]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3881,plain,
% 7.91/1.49      ( ~ arAF0_m1_pre_topc_0_1(X0) | l1_pre_topc(X0) | ~ iProver_ARSWP_112 ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_2827,c_24]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3882,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_3881]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4013,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3412,c_3882]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_20061,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_19502,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_24482,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_20061,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3431,plain,
% 7.91/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.91/1.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_21,negated_conjecture,
% 7.91/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3429,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3857,plain,
% 7.91/1.49      ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3431,c_3429]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_33581,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_24482,c_3857]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6977,plain,
% 7.91/1.49      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6623,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7556,plain,
% 7.91/1.49      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6977,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17841,plain,
% 7.91/1.49      ( r1_tarski(arAF0_sK3_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_7556,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.91/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_223,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.91/1.49      inference(bin_hyper_res,[status(thm)],[c_1,c_175]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2830,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1)
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1))
% 7.91/1.49      | ~ iProver_ARSWP_115 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_223]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3409,plain,
% 7.91/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2830]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_24984,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_17841,c_3409]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_31938,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_24984]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_32893,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_31938,c_3429]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_0,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.91/1.49      | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 7.91/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_222,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 7.91/1.49      inference(bin_hyper_res,[status(thm)],[c_0,c_175]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2829,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1)
% 7.91/1.49      | ~ iProver_ARSWP_114
% 7.91/1.49      | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_222]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3410,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
% 7.91/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2829]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_27,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2722,plain,
% 7.91/1.49      ( r1_tarski(sK7,u1_struct_0(sK6))
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2723,plain,
% 7.91/1.49      ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2722]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4622,plain,
% 7.91/1.49      ( ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.91/1.49      | ~ iProver_ARSWP_114
% 7.91/1.49      | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_2829]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4623,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_4622]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10052,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_3410,c_27,c_2723,c_4623]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_31937,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_24984]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17843,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_7556,c_3409]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_31224,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_17843]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_23,negated_conjecture,
% 7.91/1.49      ( m1_pre_topc(sK6,sK5) ),
% 7.91/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2828,negated_conjecture,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(sK6) | ~ iProver_ARSWP_113 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_23]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3411,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(sK6) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2828]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8,plain,
% 7.91/1.49      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 7.91/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2815,plain,
% 7.91/1.49      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 7.91/1.49      | arAF0_sP0_0_1(X0)
% 7.91/1.49      | ~ arAF0_sP1_0_1(X1)
% 7.91/1.49      | ~ iProver_ARSWP_100 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3422,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2815]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4668,plain,
% 7.91/1.49      ( arAF0_sP0_0_1(sK6) = iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X0) != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3411,c_3422]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5015,plain,
% 7.91/1.49      ( arAF0_sP0_0_1(sK6) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4105,c_4668]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18,plain,
% 7.91/1.49      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2825,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | ~ arAF0_sP0_0_1(X0)
% 7.91/1.49      | ~ iProver_ARSWP_110 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_18]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3414,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5117,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_3414]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8187,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_k2_struct_0_0
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13,plain,
% 7.91/1.49      ( sP0(X0,X1)
% 7.91/1.49      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
% 7.91/1.49      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2820,plain,
% 7.91/1.49      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0)))
% 7.91/1.49      | arAF0_sP0_0_1(X0)
% 7.91/1.49      | ~ iProver_ARSWP_105 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_13]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3417,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_sK2_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2820]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4856,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | r1_tarski(arAF0_sK2_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3417,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4865,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4856,c_3409]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9742,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4865,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13377,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_9742]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_21255,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_13377,c_5117]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_21270,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_21255,c_3409]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_26178,plain,
% 7.91/1.49      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_21270,c_4865,c_5117]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_26179,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_26178]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_26197,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_26179,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_26769,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_26197,c_3408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4866,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4856,c_3408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_29010,plain,
% 7.91/1.49      ( iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_26769,c_4866,c_5117]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_29011,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_29010]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_29024,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8192,c_29011]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_31041,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_29024]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_29026,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_29011,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_30725,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8192,c_29026]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_30978,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_30725]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6982,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6623,c_3409]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14829,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6982,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15016,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_14829,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15992,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15016,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22769,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15992,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_30154,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_22769]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.91/1.49      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.91/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_226,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.91/1.49      inference(bin_hyper_res,[status(thm)],[c_4,c_175]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2833,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1)
% 7.91/1.49      | ~ iProver_ARSWP_118
% 7.91/1.49      | arAF0_k7_subset_1_0 = arAF0_k4_xboole_0_0 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_226]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3406,plain,
% 7.91/1.49      ( arAF0_k7_subset_1_0 = arAF0_k4_xboole_0_0
% 7.91/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2833]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4406,plain,
% 7.91/1.49      ( arAF0_k7_subset_1_0 = arAF0_k4_xboole_0_0
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3769,c_3406]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_29025,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4406,c_29011]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_29274,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_29025,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13379,plain,
% 7.91/1.49      ( arAF0_k2_struct_0_0 = sK7
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_8186]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13376,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k2_struct_0_0
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_10052]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11484,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4406,c_4866]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_27339,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13376,c_11484]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11483,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8192,c_4866]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22190,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_11483]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_27730,plain,
% 7.91/1.49      ( iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_27339,c_5117,c_22190]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_27731,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_27730]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_27743,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_27731]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_28229,plain,
% 7.91/1.49      ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_27743,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_27744,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_27731,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5356,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_3408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13897,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8192,c_5356]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4980,plain,
% 7.91/1.49      ( ~ r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4981,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_4980]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13900,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k7_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5356,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13966,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8192,c_13900]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4057,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4058,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_4057]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4285,plain,
% 7.91/1.49      ( ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.91/1.49      | ~ iProver_ARSWP_117
% 7.91/1.49      | arAF0_k3_subset_1_0 = sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_2832]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4286,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = sK7
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_4285]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_306,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.91/1.49      theory(equality) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3834,plain,
% 7.91/1.49      ( m1_subset_1(X0,X1)
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(X2))
% 7.91/1.49      | X1 != k1_zfmisc_1(X2)
% 7.91/1.49      | X0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_306]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6586,plain,
% 7.91/1.49      ( m1_subset_1(X0,X1)
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | X1 != k1_zfmisc_1(arAF0_k2_struct_0_0)
% 7.91/1.49      | X0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_3834]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8461,plain,
% 7.91/1.49      ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | X0 != sK7
% 7.91/1.49      | k1_zfmisc_1(arAF0_k2_struct_0_0) != k1_zfmisc_1(arAF0_k2_struct_0_0) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_6586]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8462,plain,
% 7.91/1.49      ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | X0 != sK7 ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_8461]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8497,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | arAF0_k3_subset_1_0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_8462]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8498,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 != sK7
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_8497]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5355,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_3409]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8554,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_5355]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7299,plain,
% 7.91/1.49      ( ~ r1_tarski(sK7,arAF0_k2_struct_0_0)
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7300,plain,
% 7.91/1.49      ( r1_tarski(sK7,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_7299]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5408,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5355,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8551,plain,
% 7.91/1.49      ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_5408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_303,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3760,plain,
% 7.91/1.49      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_303]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4067,plain,
% 7.91/1.49      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_3760]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4068,plain,
% 7.91/1.49      ( X0 != sK7 | sK7 = X0 ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_4067]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4328,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 != sK7 | sK7 = arAF0_k3_subset_1_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_4068]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_307,plain,
% 7.91/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.91/1.49      theory(equality) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3930,plain,
% 7.91/1.49      ( r1_tarski(X0,X1)
% 7.91/1.49      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | X0 != arAF0_k2_struct_0_0
% 7.91/1.49      | X1 != arAF0_k2_struct_0_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_307]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4532,plain,
% 7.91/1.49      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.91/1.49      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | X0 != arAF0_k2_struct_0_0
% 7.91/1.49      | arAF0_k2_struct_0_0 != arAF0_k2_struct_0_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_3930]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4533,plain,
% 7.91/1.49      ( r1_tarski(X0,arAF0_k2_struct_0_0)
% 7.91/1.49      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | X0 != arAF0_k2_struct_0_0 ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_4532]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5001,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_4533]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5002,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 != arAF0_k2_struct_0_0
% 7.91/1.49      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_5001]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4060,plain,
% 7.91/1.49      ( m1_subset_1(X0,X1)
% 7.91/1.49      | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | X1 != k1_zfmisc_1(arAF0_k2_struct_0_0)
% 7.91/1.49      | X0 != arAF0_k3_subset_1_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_306]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6312,plain,
% 7.91/1.49      ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | X0 != arAF0_k3_subset_1_0
% 7.91/1.49      | k1_zfmisc_1(arAF0_k2_struct_0_0) != k1_zfmisc_1(arAF0_k2_struct_0_0) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_4060]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6313,plain,
% 7.91/1.49      ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | X0 != arAF0_k3_subset_1_0 ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_6312]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6493,plain,
% 7.91/1.49      ( ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0))
% 7.91/1.49      | sK7 != arAF0_k3_subset_1_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_6313]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6494,plain,
% 7.91/1.49      ( sK7 != arAF0_k3_subset_1_0
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_6493]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3826,plain,
% 7.91/1.49      ( r1_tarski(sK7,X0) | ~ m1_subset_1(sK7,k1_zfmisc_1(X0)) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6583,plain,
% 7.91/1.49      ( r1_tarski(sK7,arAF0_k2_struct_0_0)
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_3826]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6584,plain,
% 7.91/1.49      ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_6583]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9141,plain,
% 7.91/1.49      ( iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_8551,c_27,c_2723,c_4286,c_4328,c_4981,c_5002,c_5117,
% 7.91/1.49                 c_6494,c_6584,c_8187]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9142,plain,
% 7.91/1.49      ( r1_tarski(sK7,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_9141]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9364,plain,
% 7.91/1.49      ( iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_8554,c_27,c_2723,c_4286,c_4328,c_5002,c_5117,c_7300,
% 7.91/1.49                 c_8187,c_9282]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9365,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_9364]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18264,plain,
% 7.91/1.49      ( iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_13966,c_5002,c_5117,c_8187]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18265,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_18264]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22390,plain,
% 7.91/1.49      ( iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_13897,c_4981,c_5002,c_5117,c_8187]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22391,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_22390]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22401,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_22391]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3931,plain,
% 7.91/1.49      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3932,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_3931]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_27050,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_22401,c_3932,c_5117]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_26765,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_26197]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_26195,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_26179]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_24983,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_17841,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_26125,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.91/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_24983]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13378,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_4865]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_25924,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_13378,c_5117]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_25937,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_25924]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_19519,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_19390,c_3857]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_19716,plain,
% 7.91/1.49      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_19519]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_20006,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_19716,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_20279,plain,
% 7.91/1.49      ( l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_20006,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_25496,plain,
% 7.91/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_20279,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15014,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_14829]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15532,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15014,c_3857]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15567,plain,
% 7.91/1.49      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_15532]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_16132,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15567,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18323,plain,
% 7.91/1.49      ( l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_16132,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_25358,plain,
% 7.91/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_18323,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_24985,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_17841,c_3408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15341,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4406,c_6983]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15785,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15341,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17751,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15785,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_24764,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_17751,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_24488,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_20061,c_3857]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15797,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15341,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_16596,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15797,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17509,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_16596,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_24340,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_17509,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15515,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15014,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_16311,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15515,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_23833,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_16311,c_3857]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8190,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK2_0
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4856,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12187,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK2_0
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_8190]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_20852,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK2_0
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_12187,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_21504,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK2_0
% 7.91/1.49      | l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_20852,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_23679,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK2_0
% 7.91/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_21504,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8188,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6977,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_21550,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_8188]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_23613,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.91/1.49      | l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_21550,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10,plain,
% 7.91/1.49      ( r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 7.91/1.49      | sP0(X0,X1)
% 7.91/1.49      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
% 7.91/1.49      | k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) ),
% 7.91/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2817,plain,
% 7.91/1.49      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | arAF0_sP0_0_1(X0)
% 7.91/1.49      | ~ iProver_ARSWP_102
% 7.91/1.49      | arAF0_r2_hidden_0
% 7.91/1.49      | arAF0_k9_subset_1_0 = arAF0_sK2_0 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3420,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_102 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2817]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5747,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_102 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_3420]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_19126,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_102 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5747,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_19792,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.91/1.49      | l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_102 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_19126,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_23186,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = arAF0_sK2_0
% 7.91/1.49      | arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_102 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_19792,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_16368,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15355,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17410,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_16368,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_23096,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_17410,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15989,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_15016]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22665,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15989,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22403,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_22391]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22193,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_11483]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22192,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_11483]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11,plain,
% 7.91/1.49      ( r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
% 7.91/1.49      | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))
% 7.91/1.49      | sP0(X0,X1)
% 7.91/1.49      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2818,plain,
% 7.91/1.49      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | arAF0_sP0_0_1(X0)
% 7.91/1.49      | ~ iProver_ARSWP_103
% 7.91/1.49      | arAF0_r2_hidden_0 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3419,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_103 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2818]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5357,plain,
% 7.91/1.49      ( arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_103 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_3419]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15295,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_103 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5357,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15745,plain,
% 7.91/1.49      ( l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_103 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15295,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_21940,plain,
% 7.91/1.49      ( arAF0_sP1_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_103 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15745,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4555,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3769,c_3409]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5039,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4555,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10066,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_5039]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10430,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10066,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4658,plain,
% 7.91/1.49      ( X0 != X1 | arAF0_k3_subset_1_0 != X1 | arAF0_k3_subset_1_0 = X0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_303]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5199,plain,
% 7.91/1.49      ( X0 != arAF0_k3_subset_1_0
% 7.91/1.49      | arAF0_k3_subset_1_0 = X0
% 7.91/1.49      | arAF0_k3_subset_1_0 != arAF0_k3_subset_1_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_4658]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5200,plain,
% 7.91/1.49      ( X0 != arAF0_k3_subset_1_0 | arAF0_k3_subset_1_0 = X0 ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_5199]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6737,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
% 7.91/1.49      | arAF0_k4_xboole_0_0 != arAF0_k3_subset_1_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_5200]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_21350,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_10430,c_27,c_2723,c_4623,c_6737]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_21268,plain,
% 7.91/1.49      ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_21255]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6618,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3418,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7633,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6618,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_21022,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_sK3_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP1_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_7633,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9384,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8192,c_3946]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3660,plain,
% 7.91/1.49      ( m1_subset_1(X0,X1)
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.91/1.49      | X1 != k1_zfmisc_1(u1_struct_0(sK6))
% 7.91/1.49      | X0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_306]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4330,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,X0)
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.91/1.49      | X0 != k1_zfmisc_1(u1_struct_0(sK6))
% 7.91/1.49      | arAF0_k3_subset_1_0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_3660]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4767,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.91/1.49      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 7.91/1.49      | arAF0_k3_subset_1_0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_4330]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4768,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.91/1.49      | arAF0_k3_subset_1_0 != sK7 ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_4767]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4769,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 != sK7
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_4768]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10658,plain,
% 7.91/1.49      ( iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_9384,c_27,c_2723,c_4286,c_4769]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10659,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_10658]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13374,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_10659]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.91/1.49      | ~ sP0(X1,X2)
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.91/1.49      | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2822,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.91/1.49      | ~ arAF0_sP0_0_1(X1)
% 7.91/1.49      | ~ iProver_ARSWP_107
% 7.91/1.49      | ~ arAF0_r2_hidden_0
% 7.91/1.49      | arAF0_k9_subset_1_0 = X0 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_15]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3416,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = X0
% 7.91/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2822]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18489,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13374,c_3416]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_20472,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = arAF0_k2_struct_0_0
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_18489,c_5015]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_20067,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_19502,c_3857]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7557,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6977,c_3409]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18923,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_7557]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13591,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_5355]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9700,plain,
% 7.91/1.49      ( ~ r1_tarski(arAF0_k3_subset_1_0,sK7)
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9701,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,sK7) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_9700]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13588,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_5408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4363,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,X0)
% 7.91/1.49      | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X0)) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9322,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,sK7)
% 7.91/1.49      | ~ m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_4363]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9323,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_9322]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9265,plain,
% 7.91/1.49      ( m1_subset_1(X0,X1)
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
% 7.91/1.49      | X1 != k1_zfmisc_1(sK7)
% 7.91/1.49      | X0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_3834]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11390,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,X0)
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
% 7.91/1.49      | X0 != k1_zfmisc_1(sK7)
% 7.91/1.49      | arAF0_k3_subset_1_0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_9265]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13316,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7))
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
% 7.91/1.49      | k1_zfmisc_1(sK7) != k1_zfmisc_1(sK7)
% 7.91/1.49      | arAF0_k3_subset_1_0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_11390]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13317,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7))
% 7.91/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
% 7.91/1.49      | arAF0_k3_subset_1_0 != sK7 ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_13316]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13318,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 != sK7
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(sK7)) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_13317]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13586,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_9365]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18103,plain,
% 7.91/1.49      ( iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_13588,c_27,c_2723,c_4286,c_9323,c_13318,c_13586]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18104,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,sK7) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_18103]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18726,plain,
% 7.91/1.49      ( iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_13591,c_27,c_2723,c_4286,c_13318,c_13586]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18727,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_18726]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18738,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_18727]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18736,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k2_struct_0_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_18727]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18276,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_18265]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18115,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,sK7) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_18104]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18113,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,sK7) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_18104]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11485,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4866,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11930,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8192,c_11485]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_16889,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_11930]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17073,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK5) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_16889,c_3857]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17097,plain,
% 7.91/1.49      ( arAF0_sP0_0_1(sK5) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_17073]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17239,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_17097,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_16888,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_11930]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_16317,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_15515,c_3857]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15013,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_14829]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14814,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_6982]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13898,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4406,c_5356]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14571,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_13898]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13967,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4406,c_13900]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14461,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,sK7) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_13967]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.91/1.49      | ~ sP0(X1,X2)
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.91/1.49      | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2824,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.91/1.49      | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.91/1.49      | ~ arAF0_sP0_0_1(X1)
% 7.91/1.49      | ~ iProver_ARSWP_109
% 7.91/1.49      | ~ arAF0_r2_hidden_0 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_17]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3415,plain,
% 7.91/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2824]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5522,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3428,c_3415]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5588,plain,
% 7.91/1.49      ( r1_tarski(arAF0_sK4_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5522,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5714,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5588,c_3408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6410,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k7_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5714,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9380,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8192,c_6410]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14262,plain,
% 7.91/1.49      ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_9380]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3711,plain,
% 7.91/1.49      ( ~ r1_tarski(sK7,u1_struct_0(sK5)) ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_21,c_5]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3712,plain,
% 7.91/1.49      ( r1_tarski(sK7,u1_struct_0(sK5)) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_3711]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14356,plain,
% 7.91/1.49      ( r1_tarski(sK7,u1_struct_0(sK5)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_14262]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14359,plain,
% 7.91/1.49      ( arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_14262,c_3712,c_14356]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14370,plain,
% 7.91/1.49      ( iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_14359]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10664,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_10659]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12788,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10664,c_3416]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14211,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_12788]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5889,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = X0
% 7.91/1.49      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3431,c_3416]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10434,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10066,c_5889]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14184,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_10434]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13968,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k7_subset_1_0,sK7) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_13900]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13899,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(sK7)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_5356]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13592,plain,
% 7.91/1.49      ( r1_tarski(sK7,sK7) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13379,c_5117]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9383,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8192,c_4186]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3688,plain,
% 7.91/1.49      ( r1_tarski(X0,X1)
% 7.91/1.49      | ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.91/1.49      | X1 != u1_struct_0(sK6)
% 7.91/1.49      | X0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_307]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4329,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,X0)
% 7.91/1.49      | ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.91/1.49      | X0 != u1_struct_0(sK6)
% 7.91/1.49      | arAF0_k3_subset_1_0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_3688]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4373,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6))
% 7.91/1.49      | ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.91/1.49      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 7.91/1.49      | arAF0_k3_subset_1_0 != sK7 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_4329]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4374,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6))
% 7.91/1.49      | ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.91/1.49      | arAF0_k3_subset_1_0 != sK7 ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_4373]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4375,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 != sK7
% 7.91/1.49      | r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_4374]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10180,plain,
% 7.91/1.49      ( iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_9383,c_27,c_2723,c_4286,c_4375]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10181,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK6)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_10180]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13375,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,u1_struct_0(sK6)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_10181]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4426,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4406,c_4186]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8195,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4426,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13373,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k2_struct_0_0
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8187,c_8195]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13019,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = sK7
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8195,c_8186]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13129,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_13019,c_11484]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17842,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | l1_pre_topc(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_7556,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8189,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6623,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12198,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK3_0
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_8189]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10192,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10181,c_5889]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11987,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_10192]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11931,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4406,c_11485]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9779,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_9742]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10878,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK5) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_9779,c_3857]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10925,plain,
% 7.91/1.49      ( arAF0_sP0_0_1(sK5) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5117,c_10878]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11102,plain,
% 7.91/1.49      ( arAF0_m1_pre_topc_0_1(sK5) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10925,c_4677]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10186,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(sK6)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_10181]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10067,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_4555]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10065,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(arAF0_k2_struct_0_0)) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_5355]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5713,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5588,c_3409]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10064,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_5713]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6374,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5713,c_3430]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10063,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_6374]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10062,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,arAF0_k2_struct_0_0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_110 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_5408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10060,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_4865]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10059,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_9742]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10061,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = sK7
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_114 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10052,c_8186]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9741,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X0) = iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_105 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_4865]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8552,plain,
% 7.91/1.49      ( r1_tarski(sK7,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_6374]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_28,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8553,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_8186,c_5713]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8614,plain,
% 7.91/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_8553]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8861,plain,
% 7.91/1.49      ( arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_8552,c_28,c_8614]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8872,plain,
% 7.91/1.49      ( iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_8861]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8196,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK4_0
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5588,c_3407]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8625,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_sK4_0
% 7.91/1.49      | iProver_ARSWP_117 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_8196]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17844,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | l1_pre_topc(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_7556,c_3408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4427,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4406,c_3946]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5895,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4427,c_3416]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7771,plain,
% 7.91/1.49      ( arAF0_k4_xboole_0_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_5895]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7558,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_k7_subset_1_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_m1_pre_topc_0_1(X1) = iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_104 != iProver_top
% 7.91/1.49      | iProver_ARSWP_99 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_6977,c_3408]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5892,plain,
% 7.91/1.49      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | arAF0_sP0_0_1(X0) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5522,c_3416]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6109,plain,
% 7.91/1.49      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_5892]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7384,plain,
% 7.91/1.49      ( arAF0_sK4_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6109,c_5015]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6945,plain,
% 7.91/1.49      ( r1_tarski(arAF0_k4_xboole_0_0,u1_struct_0(X0)) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4406,c_6410]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6409,plain,
% 7.91/1.49      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_118 != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4406,c_5714]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5894,plain,
% 7.91/1.49      ( arAF0_k7_subset_1_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3946,c_3416]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6223,plain,
% 7.91/1.49      ( arAF0_k7_subset_1_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | iProver_ARSWP_116 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_5894]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5893,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4555,c_3416]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6215,plain,
% 7.91/1.49      ( arAF0_k3_subset_1_0 = arAF0_k9_subset_1_0
% 7.91/1.49      | iProver_ARSWP_115 != iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_5893]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5890,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = sK7
% 7.91/1.49      | arAF0_sP0_0_1(sK6) != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3428,c_3416]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5973,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 = sK7
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top
% 7.91/1.49      | iProver_ARSWP_107 != iProver_top
% 7.91/1.49      | iProver_ARSWP_100 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_5015,c_5890]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5521,plain,
% 7.91/1.49      ( r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 7.91/1.49      | m1_subset_1(arAF0_sK4_0,k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X1) != iProver_top
% 7.91/1.49      | iProver_ARSWP_109 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3431,c_3415]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4020,plain,
% 7.91/1.49      ( l1_pre_topc(sK6) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3411,c_4013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4181,plain,
% 7.91/1.49      ( arAF0_sP1_0_1(sK6) = iProver_top
% 7.91/1.49      | iProver_ARSWP_113 != iProver_top
% 7.91/1.49      | iProver_ARSWP_112 != iProver_top
% 7.91/1.49      | iProver_ARSWP_111 != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_4020,c_4098]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.91/1.49      | ~ r2_hidden(sK2(X2,X1),u1_pre_topc(X2))
% 7.91/1.49      | sP0(X2,X1)
% 7.91/1.49      | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.91/1.49      | k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)) != sK2(X2,X1) ),
% 7.91/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2816,plain,
% 7.91/1.49      ( ~ r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0)
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.91/1.49      | arAF0_sP0_0_1(X2)
% 7.91/1.49      | ~ iProver_ARSWP_101
% 7.91/1.49      | ~ arAF0_r2_hidden_0
% 7.91/1.49      | arAF0_k9_subset_1_0 != arAF0_sK2_0 ),
% 7.91/1.49      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3421,plain,
% 7.91/1.49      ( arAF0_k9_subset_1_0 != arAF0_sK2_0
% 7.91/1.49      | r1_tarski(arAF0_k2_struct_0_0,arAF0_k2_struct_0_0) != iProver_top
% 7.91/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.91/1.49      | arAF0_sP0_0_1(X2) = iProver_top
% 7.91/1.49      | iProver_ARSWP_101 != iProver_top
% 7.91/1.49      | arAF0_r2_hidden_0 != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_2816]) ).
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  % SZS output end Saturation for theBenchmark.p
% 7.91/1.49  
% 7.91/1.49  ------                               Statistics
% 7.91/1.49  
% 7.91/1.49  ------ Selected
% 7.91/1.49  
% 7.91/1.49  total_time:                             0.847
% 7.91/1.49  
%------------------------------------------------------------------------------
