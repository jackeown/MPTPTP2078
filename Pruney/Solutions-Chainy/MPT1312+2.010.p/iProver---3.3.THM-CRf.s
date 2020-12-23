%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:39 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 162 expanded)
%              Number of clauses        :   48 (  55 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   18
%              Number of atoms          :  340 ( 596 expanded)
%              Number of equality atoms :   76 (  82 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( ~ m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
        & m1_pre_topc(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,sK5) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    & m1_pre_topc(sK6,sK5)
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f18,f33,f32,f31])).

fof(f58,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ~ m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
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

fof(f15,plain,(
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
    inference(definition_folding,[],[f15,f20,f19])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2458,plain,
    ( sP0(X0,X1) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2470,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2456,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_336,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_19,c_5])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_407,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_408,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_410,plain,
    ( l1_pre_topc(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_24])).

cnf(c_427,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_410])).

cnf(c_428,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_2479,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK6)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2456,c_428])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2468,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2713,plain,
    ( r1_tarski(sK7,k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2479,c_2468])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2471,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2717,plain,
    ( k2_xboole_0(sK7,k1_zfmisc_1(k2_struct_0(sK6))) = k1_zfmisc_1(k2_struct_0(sK6)) ),
    inference(superposition,[status(thm)],[c_2713,c_2471])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2472,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3240,plain,
    ( r1_tarski(k1_zfmisc_1(k2_struct_0(sK6)),X0) != iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2717,c_2472])).

cnf(c_4825,plain,
    ( r1_tarski(k2_struct_0(sK6),X0) != iProver_top
    | r1_tarski(sK7,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2470,c_3240])).

cnf(c_4900,plain,
    ( sP0(sK6,X0) != iProver_top
    | r1_tarski(sK7,k1_zfmisc_1(k2_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2458,c_4825])).

cnf(c_4902,plain,
    ( sP0(sK6,sK5) != iProver_top
    | r1_tarski(sK7,k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4900])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2469,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2457,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_422,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_24])).

cnf(c_423,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_2482,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK5)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2457,c_423])).

cnf(c_2838,plain,
    ( r1_tarski(sK7,k1_zfmisc_1(k2_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_2482])).

cnf(c_18,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_350,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_18,c_7])).

cnf(c_354,plain,
    ( ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_20])).

cnf(c_355,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_396,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_355,c_23])).

cnf(c_397,plain,
    ( sP0(sK6,sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_398,plain,
    ( sP0(sK6,sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_25,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4902,c_2838,c_398,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.07/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.03  
% 2.07/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.07/1.03  
% 2.07/1.03  ------  iProver source info
% 2.07/1.03  
% 2.07/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.07/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.07/1.03  git: non_committed_changes: false
% 2.07/1.03  git: last_make_outside_of_git: false
% 2.07/1.03  
% 2.07/1.03  ------ 
% 2.07/1.03  
% 2.07/1.03  ------ Input Options
% 2.07/1.03  
% 2.07/1.03  --out_options                           all
% 2.07/1.03  --tptp_safe_out                         true
% 2.07/1.03  --problem_path                          ""
% 2.07/1.03  --include_path                          ""
% 2.07/1.03  --clausifier                            res/vclausify_rel
% 2.07/1.03  --clausifier_options                    --mode clausify
% 2.07/1.03  --stdin                                 false
% 2.07/1.03  --stats_out                             all
% 2.07/1.03  
% 2.07/1.03  ------ General Options
% 2.07/1.03  
% 2.07/1.03  --fof                                   false
% 2.07/1.03  --time_out_real                         305.
% 2.07/1.03  --time_out_virtual                      -1.
% 2.07/1.03  --symbol_type_check                     false
% 2.07/1.03  --clausify_out                          false
% 2.07/1.03  --sig_cnt_out                           false
% 2.07/1.03  --trig_cnt_out                          false
% 2.07/1.03  --trig_cnt_out_tolerance                1.
% 2.07/1.03  --trig_cnt_out_sk_spl                   false
% 2.07/1.03  --abstr_cl_out                          false
% 2.07/1.03  
% 2.07/1.03  ------ Global Options
% 2.07/1.03  
% 2.07/1.03  --schedule                              default
% 2.07/1.03  --add_important_lit                     false
% 2.07/1.03  --prop_solver_per_cl                    1000
% 2.07/1.03  --min_unsat_core                        false
% 2.07/1.03  --soft_assumptions                      false
% 2.07/1.03  --soft_lemma_size                       3
% 2.07/1.03  --prop_impl_unit_size                   0
% 2.07/1.03  --prop_impl_unit                        []
% 2.07/1.03  --share_sel_clauses                     true
% 2.07/1.03  --reset_solvers                         false
% 2.07/1.03  --bc_imp_inh                            [conj_cone]
% 2.07/1.03  --conj_cone_tolerance                   3.
% 2.07/1.03  --extra_neg_conj                        none
% 2.07/1.03  --large_theory_mode                     true
% 2.07/1.03  --prolific_symb_bound                   200
% 2.07/1.03  --lt_threshold                          2000
% 2.07/1.03  --clause_weak_htbl                      true
% 2.07/1.03  --gc_record_bc_elim                     false
% 2.07/1.03  
% 2.07/1.03  ------ Preprocessing Options
% 2.07/1.03  
% 2.07/1.03  --preprocessing_flag                    true
% 2.07/1.03  --time_out_prep_mult                    0.1
% 2.07/1.03  --splitting_mode                        input
% 2.07/1.03  --splitting_grd                         true
% 2.07/1.03  --splitting_cvd                         false
% 2.07/1.03  --splitting_cvd_svl                     false
% 2.07/1.03  --splitting_nvd                         32
% 2.07/1.03  --sub_typing                            true
% 2.07/1.03  --prep_gs_sim                           true
% 2.07/1.03  --prep_unflatten                        true
% 2.07/1.03  --prep_res_sim                          true
% 2.07/1.03  --prep_upred                            true
% 2.07/1.03  --prep_sem_filter                       exhaustive
% 2.07/1.03  --prep_sem_filter_out                   false
% 2.07/1.03  --pred_elim                             true
% 2.07/1.03  --res_sim_input                         true
% 2.07/1.03  --eq_ax_congr_red                       true
% 2.07/1.03  --pure_diseq_elim                       true
% 2.07/1.03  --brand_transform                       false
% 2.07/1.03  --non_eq_to_eq                          false
% 2.07/1.03  --prep_def_merge                        true
% 2.07/1.03  --prep_def_merge_prop_impl              false
% 2.07/1.03  --prep_def_merge_mbd                    true
% 2.07/1.03  --prep_def_merge_tr_red                 false
% 2.07/1.03  --prep_def_merge_tr_cl                  false
% 2.07/1.03  --smt_preprocessing                     true
% 2.07/1.03  --smt_ac_axioms                         fast
% 2.07/1.03  --preprocessed_out                      false
% 2.07/1.03  --preprocessed_stats                    false
% 2.07/1.03  
% 2.07/1.03  ------ Abstraction refinement Options
% 2.07/1.03  
% 2.07/1.03  --abstr_ref                             []
% 2.07/1.03  --abstr_ref_prep                        false
% 2.07/1.03  --abstr_ref_until_sat                   false
% 2.07/1.03  --abstr_ref_sig_restrict                funpre
% 2.07/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/1.03  --abstr_ref_under                       []
% 2.07/1.03  
% 2.07/1.03  ------ SAT Options
% 2.07/1.03  
% 2.07/1.03  --sat_mode                              false
% 2.07/1.03  --sat_fm_restart_options                ""
% 2.07/1.03  --sat_gr_def                            false
% 2.07/1.03  --sat_epr_types                         true
% 2.07/1.03  --sat_non_cyclic_types                  false
% 2.07/1.03  --sat_finite_models                     false
% 2.07/1.03  --sat_fm_lemmas                         false
% 2.07/1.03  --sat_fm_prep                           false
% 2.07/1.03  --sat_fm_uc_incr                        true
% 2.07/1.03  --sat_out_model                         small
% 2.07/1.03  --sat_out_clauses                       false
% 2.07/1.03  
% 2.07/1.03  ------ QBF Options
% 2.07/1.03  
% 2.07/1.03  --qbf_mode                              false
% 2.07/1.03  --qbf_elim_univ                         false
% 2.07/1.03  --qbf_dom_inst                          none
% 2.07/1.03  --qbf_dom_pre_inst                      false
% 2.07/1.03  --qbf_sk_in                             false
% 2.07/1.03  --qbf_pred_elim                         true
% 2.07/1.03  --qbf_split                             512
% 2.07/1.03  
% 2.07/1.03  ------ BMC1 Options
% 2.07/1.03  
% 2.07/1.03  --bmc1_incremental                      false
% 2.07/1.03  --bmc1_axioms                           reachable_all
% 2.07/1.03  --bmc1_min_bound                        0
% 2.07/1.03  --bmc1_max_bound                        -1
% 2.07/1.03  --bmc1_max_bound_default                -1
% 2.07/1.03  --bmc1_symbol_reachability              true
% 2.07/1.03  --bmc1_property_lemmas                  false
% 2.07/1.03  --bmc1_k_induction                      false
% 2.07/1.03  --bmc1_non_equiv_states                 false
% 2.07/1.03  --bmc1_deadlock                         false
% 2.07/1.03  --bmc1_ucm                              false
% 2.07/1.03  --bmc1_add_unsat_core                   none
% 2.07/1.03  --bmc1_unsat_core_children              false
% 2.07/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/1.03  --bmc1_out_stat                         full
% 2.07/1.03  --bmc1_ground_init                      false
% 2.07/1.03  --bmc1_pre_inst_next_state              false
% 2.07/1.03  --bmc1_pre_inst_state                   false
% 2.07/1.03  --bmc1_pre_inst_reach_state             false
% 2.07/1.03  --bmc1_out_unsat_core                   false
% 2.07/1.03  --bmc1_aig_witness_out                  false
% 2.07/1.03  --bmc1_verbose                          false
% 2.07/1.03  --bmc1_dump_clauses_tptp                false
% 2.07/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.07/1.03  --bmc1_dump_file                        -
% 2.07/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.07/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.07/1.03  --bmc1_ucm_extend_mode                  1
% 2.07/1.03  --bmc1_ucm_init_mode                    2
% 2.07/1.03  --bmc1_ucm_cone_mode                    none
% 2.07/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.07/1.03  --bmc1_ucm_relax_model                  4
% 2.07/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.07/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/1.03  --bmc1_ucm_layered_model                none
% 2.07/1.03  --bmc1_ucm_max_lemma_size               10
% 2.07/1.03  
% 2.07/1.03  ------ AIG Options
% 2.07/1.03  
% 2.07/1.03  --aig_mode                              false
% 2.07/1.03  
% 2.07/1.03  ------ Instantiation Options
% 2.07/1.03  
% 2.07/1.03  --instantiation_flag                    true
% 2.07/1.03  --inst_sos_flag                         false
% 2.07/1.03  --inst_sos_phase                        true
% 2.07/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/1.03  --inst_lit_sel_side                     num_symb
% 2.07/1.03  --inst_solver_per_active                1400
% 2.07/1.03  --inst_solver_calls_frac                1.
% 2.07/1.03  --inst_passive_queue_type               priority_queues
% 2.07/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/1.03  --inst_passive_queues_freq              [25;2]
% 2.07/1.03  --inst_dismatching                      true
% 2.07/1.03  --inst_eager_unprocessed_to_passive     true
% 2.07/1.03  --inst_prop_sim_given                   true
% 2.07/1.03  --inst_prop_sim_new                     false
% 2.07/1.03  --inst_subs_new                         false
% 2.07/1.03  --inst_eq_res_simp                      false
% 2.07/1.03  --inst_subs_given                       false
% 2.07/1.03  --inst_orphan_elimination               true
% 2.07/1.03  --inst_learning_loop_flag               true
% 2.07/1.03  --inst_learning_start                   3000
% 2.07/1.03  --inst_learning_factor                  2
% 2.07/1.03  --inst_start_prop_sim_after_learn       3
% 2.07/1.03  --inst_sel_renew                        solver
% 2.07/1.03  --inst_lit_activity_flag                true
% 2.07/1.03  --inst_restr_to_given                   false
% 2.07/1.03  --inst_activity_threshold               500
% 2.07/1.03  --inst_out_proof                        true
% 2.07/1.03  
% 2.07/1.03  ------ Resolution Options
% 2.07/1.03  
% 2.07/1.03  --resolution_flag                       true
% 2.07/1.03  --res_lit_sel                           adaptive
% 2.07/1.03  --res_lit_sel_side                      none
% 2.07/1.03  --res_ordering                          kbo
% 2.07/1.03  --res_to_prop_solver                    active
% 2.07/1.03  --res_prop_simpl_new                    false
% 2.07/1.03  --res_prop_simpl_given                  true
% 2.07/1.03  --res_passive_queue_type                priority_queues
% 2.07/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/1.03  --res_passive_queues_freq               [15;5]
% 2.07/1.03  --res_forward_subs                      full
% 2.07/1.03  --res_backward_subs                     full
% 2.07/1.03  --res_forward_subs_resolution           true
% 2.07/1.03  --res_backward_subs_resolution          true
% 2.07/1.03  --res_orphan_elimination                true
% 2.07/1.03  --res_time_limit                        2.
% 2.07/1.03  --res_out_proof                         true
% 2.07/1.03  
% 2.07/1.03  ------ Superposition Options
% 2.07/1.03  
% 2.07/1.03  --superposition_flag                    true
% 2.07/1.03  --sup_passive_queue_type                priority_queues
% 2.07/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.07/1.03  --demod_completeness_check              fast
% 2.07/1.03  --demod_use_ground                      true
% 2.07/1.03  --sup_to_prop_solver                    passive
% 2.07/1.03  --sup_prop_simpl_new                    true
% 2.07/1.03  --sup_prop_simpl_given                  true
% 2.07/1.03  --sup_fun_splitting                     false
% 2.07/1.03  --sup_smt_interval                      50000
% 2.07/1.03  
% 2.07/1.03  ------ Superposition Simplification Setup
% 2.07/1.03  
% 2.07/1.03  --sup_indices_passive                   []
% 2.07/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.03  --sup_full_bw                           [BwDemod]
% 2.07/1.03  --sup_immed_triv                        [TrivRules]
% 2.07/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.03  --sup_immed_bw_main                     []
% 2.07/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/1.03  
% 2.07/1.03  ------ Combination Options
% 2.07/1.03  
% 2.07/1.03  --comb_res_mult                         3
% 2.07/1.03  --comb_sup_mult                         2
% 2.07/1.03  --comb_inst_mult                        10
% 2.07/1.03  
% 2.07/1.03  ------ Debug Options
% 2.07/1.03  
% 2.07/1.03  --dbg_backtrace                         false
% 2.07/1.03  --dbg_dump_prop_clauses                 false
% 2.07/1.03  --dbg_dump_prop_clauses_file            -
% 2.07/1.03  --dbg_out_stat                          false
% 2.07/1.03  ------ Parsing...
% 2.07/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.07/1.03  
% 2.07/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.07/1.03  
% 2.07/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.07/1.03  
% 2.07/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.07/1.03  ------ Proving...
% 2.07/1.03  ------ Problem Properties 
% 2.07/1.03  
% 2.07/1.03  
% 2.07/1.03  clauses                                 20
% 2.07/1.03  conjectures                             2
% 2.07/1.03  EPR                                     1
% 2.07/1.03  Horn                                    16
% 2.07/1.03  unary                                   5
% 2.07/1.03  binary                                  6
% 2.07/1.03  lits                                    55
% 2.07/1.03  lits eq                                 6
% 2.07/1.03  fd_pure                                 0
% 2.07/1.03  fd_pseudo                               0
% 2.07/1.03  fd_cond                                 0
% 2.07/1.03  fd_pseudo_cond                          0
% 2.07/1.03  AC symbols                              0
% 2.07/1.03  
% 2.07/1.03  ------ Schedule dynamic 5 is on 
% 2.07/1.03  
% 2.07/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.07/1.03  
% 2.07/1.03  
% 2.07/1.03  ------ 
% 2.07/1.03  Current options:
% 2.07/1.03  ------ 
% 2.07/1.03  
% 2.07/1.03  ------ Input Options
% 2.07/1.03  
% 2.07/1.03  --out_options                           all
% 2.07/1.03  --tptp_safe_out                         true
% 2.07/1.03  --problem_path                          ""
% 2.07/1.03  --include_path                          ""
% 2.07/1.03  --clausifier                            res/vclausify_rel
% 2.07/1.03  --clausifier_options                    --mode clausify
% 2.07/1.03  --stdin                                 false
% 2.07/1.03  --stats_out                             all
% 2.07/1.03  
% 2.07/1.03  ------ General Options
% 2.07/1.03  
% 2.07/1.03  --fof                                   false
% 2.07/1.03  --time_out_real                         305.
% 2.07/1.03  --time_out_virtual                      -1.
% 2.07/1.03  --symbol_type_check                     false
% 2.07/1.03  --clausify_out                          false
% 2.07/1.03  --sig_cnt_out                           false
% 2.07/1.03  --trig_cnt_out                          false
% 2.07/1.03  --trig_cnt_out_tolerance                1.
% 2.07/1.03  --trig_cnt_out_sk_spl                   false
% 2.07/1.03  --abstr_cl_out                          false
% 2.07/1.03  
% 2.07/1.03  ------ Global Options
% 2.07/1.03  
% 2.07/1.03  --schedule                              default
% 2.07/1.03  --add_important_lit                     false
% 2.07/1.03  --prop_solver_per_cl                    1000
% 2.07/1.03  --min_unsat_core                        false
% 2.07/1.03  --soft_assumptions                      false
% 2.07/1.03  --soft_lemma_size                       3
% 2.07/1.03  --prop_impl_unit_size                   0
% 2.07/1.03  --prop_impl_unit                        []
% 2.07/1.03  --share_sel_clauses                     true
% 2.07/1.03  --reset_solvers                         false
% 2.07/1.03  --bc_imp_inh                            [conj_cone]
% 2.07/1.03  --conj_cone_tolerance                   3.
% 2.07/1.03  --extra_neg_conj                        none
% 2.07/1.03  --large_theory_mode                     true
% 2.07/1.03  --prolific_symb_bound                   200
% 2.07/1.03  --lt_threshold                          2000
% 2.07/1.03  --clause_weak_htbl                      true
% 2.07/1.03  --gc_record_bc_elim                     false
% 2.07/1.03  
% 2.07/1.03  ------ Preprocessing Options
% 2.07/1.03  
% 2.07/1.03  --preprocessing_flag                    true
% 2.07/1.03  --time_out_prep_mult                    0.1
% 2.07/1.03  --splitting_mode                        input
% 2.07/1.03  --splitting_grd                         true
% 2.07/1.03  --splitting_cvd                         false
% 2.07/1.03  --splitting_cvd_svl                     false
% 2.07/1.03  --splitting_nvd                         32
% 2.07/1.03  --sub_typing                            true
% 2.07/1.03  --prep_gs_sim                           true
% 2.07/1.03  --prep_unflatten                        true
% 2.07/1.03  --prep_res_sim                          true
% 2.07/1.03  --prep_upred                            true
% 2.07/1.03  --prep_sem_filter                       exhaustive
% 2.07/1.03  --prep_sem_filter_out                   false
% 2.07/1.03  --pred_elim                             true
% 2.07/1.03  --res_sim_input                         true
% 2.07/1.03  --eq_ax_congr_red                       true
% 2.07/1.03  --pure_diseq_elim                       true
% 2.07/1.03  --brand_transform                       false
% 2.07/1.03  --non_eq_to_eq                          false
% 2.07/1.03  --prep_def_merge                        true
% 2.07/1.03  --prep_def_merge_prop_impl              false
% 2.07/1.03  --prep_def_merge_mbd                    true
% 2.07/1.03  --prep_def_merge_tr_red                 false
% 2.07/1.03  --prep_def_merge_tr_cl                  false
% 2.07/1.03  --smt_preprocessing                     true
% 2.07/1.03  --smt_ac_axioms                         fast
% 2.07/1.03  --preprocessed_out                      false
% 2.07/1.03  --preprocessed_stats                    false
% 2.07/1.03  
% 2.07/1.03  ------ Abstraction refinement Options
% 2.07/1.03  
% 2.07/1.03  --abstr_ref                             []
% 2.07/1.03  --abstr_ref_prep                        false
% 2.07/1.03  --abstr_ref_until_sat                   false
% 2.07/1.03  --abstr_ref_sig_restrict                funpre
% 2.07/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/1.03  --abstr_ref_under                       []
% 2.07/1.03  
% 2.07/1.03  ------ SAT Options
% 2.07/1.03  
% 2.07/1.03  --sat_mode                              false
% 2.07/1.03  --sat_fm_restart_options                ""
% 2.07/1.03  --sat_gr_def                            false
% 2.07/1.03  --sat_epr_types                         true
% 2.07/1.03  --sat_non_cyclic_types                  false
% 2.07/1.03  --sat_finite_models                     false
% 2.07/1.03  --sat_fm_lemmas                         false
% 2.07/1.03  --sat_fm_prep                           false
% 2.07/1.03  --sat_fm_uc_incr                        true
% 2.07/1.03  --sat_out_model                         small
% 2.07/1.03  --sat_out_clauses                       false
% 2.07/1.03  
% 2.07/1.03  ------ QBF Options
% 2.07/1.03  
% 2.07/1.03  --qbf_mode                              false
% 2.07/1.03  --qbf_elim_univ                         false
% 2.07/1.03  --qbf_dom_inst                          none
% 2.07/1.03  --qbf_dom_pre_inst                      false
% 2.07/1.03  --qbf_sk_in                             false
% 2.07/1.03  --qbf_pred_elim                         true
% 2.07/1.03  --qbf_split                             512
% 2.07/1.03  
% 2.07/1.03  ------ BMC1 Options
% 2.07/1.03  
% 2.07/1.03  --bmc1_incremental                      false
% 2.07/1.03  --bmc1_axioms                           reachable_all
% 2.07/1.03  --bmc1_min_bound                        0
% 2.07/1.03  --bmc1_max_bound                        -1
% 2.07/1.03  --bmc1_max_bound_default                -1
% 2.07/1.03  --bmc1_symbol_reachability              true
% 2.07/1.03  --bmc1_property_lemmas                  false
% 2.07/1.03  --bmc1_k_induction                      false
% 2.07/1.03  --bmc1_non_equiv_states                 false
% 2.07/1.03  --bmc1_deadlock                         false
% 2.07/1.03  --bmc1_ucm                              false
% 2.07/1.03  --bmc1_add_unsat_core                   none
% 2.07/1.03  --bmc1_unsat_core_children              false
% 2.07/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/1.03  --bmc1_out_stat                         full
% 2.07/1.03  --bmc1_ground_init                      false
% 2.07/1.03  --bmc1_pre_inst_next_state              false
% 2.07/1.03  --bmc1_pre_inst_state                   false
% 2.07/1.03  --bmc1_pre_inst_reach_state             false
% 2.07/1.03  --bmc1_out_unsat_core                   false
% 2.07/1.03  --bmc1_aig_witness_out                  false
% 2.07/1.03  --bmc1_verbose                          false
% 2.07/1.03  --bmc1_dump_clauses_tptp                false
% 2.07/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.07/1.03  --bmc1_dump_file                        -
% 2.07/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.07/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.07/1.03  --bmc1_ucm_extend_mode                  1
% 2.07/1.03  --bmc1_ucm_init_mode                    2
% 2.07/1.03  --bmc1_ucm_cone_mode                    none
% 2.07/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.07/1.03  --bmc1_ucm_relax_model                  4
% 2.07/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.07/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/1.03  --bmc1_ucm_layered_model                none
% 2.07/1.03  --bmc1_ucm_max_lemma_size               10
% 2.07/1.03  
% 2.07/1.03  ------ AIG Options
% 2.07/1.03  
% 2.07/1.03  --aig_mode                              false
% 2.07/1.03  
% 2.07/1.03  ------ Instantiation Options
% 2.07/1.03  
% 2.07/1.03  --instantiation_flag                    true
% 2.07/1.03  --inst_sos_flag                         false
% 2.07/1.03  --inst_sos_phase                        true
% 2.07/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/1.03  --inst_lit_sel_side                     none
% 2.07/1.03  --inst_solver_per_active                1400
% 2.07/1.03  --inst_solver_calls_frac                1.
% 2.07/1.03  --inst_passive_queue_type               priority_queues
% 2.07/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/1.03  --inst_passive_queues_freq              [25;2]
% 2.07/1.03  --inst_dismatching                      true
% 2.07/1.03  --inst_eager_unprocessed_to_passive     true
% 2.07/1.03  --inst_prop_sim_given                   true
% 2.07/1.03  --inst_prop_sim_new                     false
% 2.07/1.03  --inst_subs_new                         false
% 2.07/1.03  --inst_eq_res_simp                      false
% 2.07/1.03  --inst_subs_given                       false
% 2.07/1.03  --inst_orphan_elimination               true
% 2.07/1.03  --inst_learning_loop_flag               true
% 2.07/1.03  --inst_learning_start                   3000
% 2.07/1.03  --inst_learning_factor                  2
% 2.07/1.03  --inst_start_prop_sim_after_learn       3
% 2.07/1.03  --inst_sel_renew                        solver
% 2.07/1.03  --inst_lit_activity_flag                true
% 2.07/1.03  --inst_restr_to_given                   false
% 2.07/1.03  --inst_activity_threshold               500
% 2.07/1.03  --inst_out_proof                        true
% 2.07/1.03  
% 2.07/1.03  ------ Resolution Options
% 2.07/1.03  
% 2.07/1.03  --resolution_flag                       false
% 2.07/1.03  --res_lit_sel                           adaptive
% 2.07/1.03  --res_lit_sel_side                      none
% 2.07/1.03  --res_ordering                          kbo
% 2.07/1.03  --res_to_prop_solver                    active
% 2.07/1.03  --res_prop_simpl_new                    false
% 2.07/1.03  --res_prop_simpl_given                  true
% 2.07/1.03  --res_passive_queue_type                priority_queues
% 2.07/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/1.03  --res_passive_queues_freq               [15;5]
% 2.07/1.03  --res_forward_subs                      full
% 2.07/1.03  --res_backward_subs                     full
% 2.07/1.03  --res_forward_subs_resolution           true
% 2.07/1.03  --res_backward_subs_resolution          true
% 2.07/1.03  --res_orphan_elimination                true
% 2.07/1.03  --res_time_limit                        2.
% 2.07/1.03  --res_out_proof                         true
% 2.07/1.03  
% 2.07/1.03  ------ Superposition Options
% 2.07/1.03  
% 2.07/1.03  --superposition_flag                    true
% 2.07/1.03  --sup_passive_queue_type                priority_queues
% 2.07/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.07/1.03  --demod_completeness_check              fast
% 2.07/1.03  --demod_use_ground                      true
% 2.07/1.03  --sup_to_prop_solver                    passive
% 2.07/1.03  --sup_prop_simpl_new                    true
% 2.07/1.03  --sup_prop_simpl_given                  true
% 2.07/1.03  --sup_fun_splitting                     false
% 2.07/1.03  --sup_smt_interval                      50000
% 2.07/1.03  
% 2.07/1.03  ------ Superposition Simplification Setup
% 2.07/1.03  
% 2.07/1.03  --sup_indices_passive                   []
% 2.07/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.03  --sup_full_bw                           [BwDemod]
% 2.07/1.03  --sup_immed_triv                        [TrivRules]
% 2.07/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.03  --sup_immed_bw_main                     []
% 2.07/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/1.03  
% 2.07/1.03  ------ Combination Options
% 2.07/1.03  
% 2.07/1.03  --comb_res_mult                         3
% 2.07/1.03  --comb_sup_mult                         2
% 2.07/1.03  --comb_inst_mult                        10
% 2.07/1.03  
% 2.07/1.03  ------ Debug Options
% 2.07/1.03  
% 2.07/1.03  --dbg_backtrace                         false
% 2.07/1.03  --dbg_dump_prop_clauses                 false
% 2.07/1.03  --dbg_dump_prop_clauses_file            -
% 2.07/1.03  --dbg_out_stat                          false
% 2.07/1.03  
% 2.07/1.03  
% 2.07/1.03  
% 2.07/1.03  
% 2.07/1.03  ------ Proving...
% 2.07/1.03  
% 2.07/1.03  
% 2.07/1.03  % SZS status Theorem for theBenchmark.p
% 2.07/1.03  
% 2.07/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.07/1.03  
% 2.07/1.03  fof(f19,plain,(
% 2.07/1.03    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 2.07/1.03    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.07/1.03  
% 2.07/1.03  fof(f24,plain,(
% 2.07/1.03    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 2.07/1.03    inference(nnf_transformation,[],[f19])).
% 2.07/1.03  
% 2.07/1.03  fof(f25,plain,(
% 2.07/1.03    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 2.07/1.03    inference(flattening,[],[f24])).
% 2.07/1.03  
% 2.07/1.03  fof(f26,plain,(
% 2.07/1.03    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 2.07/1.03    inference(rectify,[],[f25])).
% 2.07/1.03  
% 2.07/1.03  fof(f29,plain,(
% 2.07/1.03    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.07/1.03    introduced(choice_axiom,[])).
% 2.07/1.03  
% 2.07/1.03  fof(f28,plain,(
% 2.07/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 2.07/1.03    introduced(choice_axiom,[])).
% 2.07/1.03  
% 2.07/1.03  fof(f27,plain,(
% 2.07/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.07/1.03    introduced(choice_axiom,[])).
% 2.07/1.03  
% 2.07/1.03  fof(f30,plain,(
% 2.07/1.03    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 2.07/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f29,f28,f27])).
% 2.07/1.03  
% 2.07/1.03  fof(f43,plain,(
% 2.07/1.03    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 2.07/1.03    inference(cnf_transformation,[],[f30])).
% 2.07/1.03  
% 2.07/1.03  fof(f3,axiom,(
% 2.07/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 2.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.03  
% 2.07/1.03  fof(f13,plain,(
% 2.07/1.03    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.07/1.03    inference(ennf_transformation,[],[f3])).
% 2.07/1.03  
% 2.07/1.03  fof(f37,plain,(
% 2.07/1.03    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.07/1.03    inference(cnf_transformation,[],[f13])).
% 2.07/1.03  
% 2.07/1.03  fof(f9,conjecture,(
% 2.07/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.03  
% 2.07/1.03  fof(f10,negated_conjecture,(
% 2.07/1.03    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.07/1.03    inference(negated_conjecture,[],[f9])).
% 2.07/1.03  
% 2.07/1.03  fof(f18,plain,(
% 2.07/1.03    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 2.07/1.03    inference(ennf_transformation,[],[f10])).
% 2.07/1.03  
% 2.07/1.03  fof(f33,plain,(
% 2.07/1.03    ( ! [X0,X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) => (~m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 2.07/1.03    introduced(choice_axiom,[])).
% 2.07/1.03  
% 2.07/1.03  fof(f32,plain,(
% 2.07/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) => (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))) & m1_pre_topc(sK6,X0))) )),
% 2.07/1.03    introduced(choice_axiom,[])).
% 2.07/1.03  
% 2.07/1.03  fof(f31,plain,(
% 2.07/1.03    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,sK5)) & l1_pre_topc(sK5))),
% 2.07/1.03    introduced(choice_axiom,[])).
% 2.07/1.03  
% 2.07/1.03  fof(f34,plain,(
% 2.07/1.03    ((~m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))) & m1_pre_topc(sK6,sK5)) & l1_pre_topc(sK5)),
% 2.07/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f18,f33,f32,f31])).
% 2.07/1.03  
% 2.07/1.03  fof(f58,plain,(
% 2.07/1.03    m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))),
% 2.07/1.03    inference(cnf_transformation,[],[f34])).
% 2.07/1.03  
% 2.07/1.03  fof(f7,axiom,(
% 2.07/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.03  
% 2.07/1.03  fof(f16,plain,(
% 2.07/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.07/1.03    inference(ennf_transformation,[],[f7])).
% 2.07/1.03  
% 2.07/1.03  fof(f54,plain,(
% 2.07/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.07/1.03    inference(cnf_transformation,[],[f16])).
% 2.07/1.03  
% 2.07/1.03  fof(f5,axiom,(
% 2.07/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.03  
% 2.07/1.03  fof(f14,plain,(
% 2.07/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.07/1.03    inference(ennf_transformation,[],[f5])).
% 2.07/1.03  
% 2.07/1.03  fof(f40,plain,(
% 2.07/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.07/1.03    inference(cnf_transformation,[],[f14])).
% 2.07/1.03  
% 2.07/1.03  fof(f8,axiom,(
% 2.07/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.03  
% 2.07/1.03  fof(f17,plain,(
% 2.07/1.03    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.07/1.03    inference(ennf_transformation,[],[f8])).
% 2.07/1.03  
% 2.07/1.03  fof(f55,plain,(
% 2.07/1.03    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.07/1.03    inference(cnf_transformation,[],[f17])).
% 2.07/1.03  
% 2.07/1.03  fof(f57,plain,(
% 2.07/1.03    m1_pre_topc(sK6,sK5)),
% 2.07/1.03    inference(cnf_transformation,[],[f34])).
% 2.07/1.03  
% 2.07/1.03  fof(f56,plain,(
% 2.07/1.03    l1_pre_topc(sK5)),
% 2.07/1.03    inference(cnf_transformation,[],[f34])).
% 2.07/1.03  
% 2.07/1.03  fof(f4,axiom,(
% 2.07/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.03  
% 2.07/1.03  fof(f22,plain,(
% 2.07/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.07/1.03    inference(nnf_transformation,[],[f4])).
% 2.07/1.03  
% 2.07/1.03  fof(f38,plain,(
% 2.07/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.07/1.03    inference(cnf_transformation,[],[f22])).
% 2.07/1.03  
% 2.07/1.03  fof(f2,axiom,(
% 2.07/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.03  
% 2.07/1.03  fof(f12,plain,(
% 2.07/1.03    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.07/1.03    inference(ennf_transformation,[],[f2])).
% 2.07/1.03  
% 2.07/1.03  fof(f36,plain,(
% 2.07/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.07/1.03    inference(cnf_transformation,[],[f12])).
% 2.07/1.03  
% 2.07/1.03  fof(f1,axiom,(
% 2.07/1.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.03  
% 2.07/1.03  fof(f11,plain,(
% 2.07/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.07/1.03    inference(ennf_transformation,[],[f1])).
% 2.07/1.03  
% 2.07/1.03  fof(f35,plain,(
% 2.07/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 2.07/1.03    inference(cnf_transformation,[],[f11])).
% 2.07/1.03  
% 2.07/1.03  fof(f39,plain,(
% 2.07/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.07/1.03    inference(cnf_transformation,[],[f22])).
% 2.07/1.03  
% 2.07/1.03  fof(f59,plain,(
% 2.07/1.03    ~m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))),
% 2.07/1.03    inference(cnf_transformation,[],[f34])).
% 2.07/1.03  
% 2.07/1.03  fof(f6,axiom,(
% 2.07/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 2.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.03  
% 2.07/1.03  fof(f15,plain,(
% 2.07/1.03    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.07/1.03    inference(ennf_transformation,[],[f6])).
% 2.07/1.03  
% 2.07/1.03  fof(f20,plain,(
% 2.07/1.03    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 2.07/1.03    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.07/1.03  
% 2.07/1.03  fof(f21,plain,(
% 2.07/1.03    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.07/1.03    inference(definition_folding,[],[f15,f20,f19])).
% 2.07/1.03  
% 2.07/1.03  fof(f53,plain,(
% 2.07/1.03    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.07/1.03    inference(cnf_transformation,[],[f21])).
% 2.07/1.03  
% 2.07/1.03  fof(f23,plain,(
% 2.07/1.03    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 2.07/1.03    inference(nnf_transformation,[],[f20])).
% 2.07/1.03  
% 2.07/1.03  fof(f41,plain,(
% 2.07/1.03    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 2.07/1.03    inference(cnf_transformation,[],[f23])).
% 2.07/1.03  
% 2.07/1.03  cnf(c_17,plain,
% 2.07/1.03      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 2.07/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2458,plain,
% 2.07/1.03      ( sP0(X0,X1) != iProver_top
% 2.07/1.03      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
% 2.07/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2,plain,
% 2.07/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 2.07/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2470,plain,
% 2.07/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.07/1.03      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.07/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_22,negated_conjecture,
% 2.07/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
% 2.07/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2456,plain,
% 2.07/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top ),
% 2.07/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_19,plain,
% 2.07/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.07/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_5,plain,
% 2.07/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.07/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_336,plain,
% 2.07/1.03      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.07/1.03      inference(resolution,[status(thm)],[c_19,c_5]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_20,plain,
% 2.07/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.07/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_23,negated_conjecture,
% 2.07/1.03      ( m1_pre_topc(sK6,sK5) ),
% 2.07/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_407,plain,
% 2.07/1.03      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X1 | sK5 != X0 ),
% 2.07/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_23]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_408,plain,
% 2.07/1.03      ( l1_pre_topc(sK6) | ~ l1_pre_topc(sK5) ),
% 2.07/1.03      inference(unflattening,[status(thm)],[c_407]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_24,negated_conjecture,
% 2.07/1.03      ( l1_pre_topc(sK5) ),
% 2.07/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_410,plain,
% 2.07/1.03      ( l1_pre_topc(sK6) ),
% 2.07/1.03      inference(global_propositional_subsumption,
% 2.07/1.03                [status(thm)],
% 2.07/1.03                [c_408,c_24]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_427,plain,
% 2.07/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK6 != X0 ),
% 2.07/1.03      inference(resolution_lifted,[status(thm)],[c_336,c_410]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_428,plain,
% 2.07/1.03      ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
% 2.07/1.03      inference(unflattening,[status(thm)],[c_427]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2479,plain,
% 2.07/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK6)))) = iProver_top ),
% 2.07/1.03      inference(light_normalisation,[status(thm)],[c_2456,c_428]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_4,plain,
% 2.07/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.07/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2468,plain,
% 2.07/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.07/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.07/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2713,plain,
% 2.07/1.03      ( r1_tarski(sK7,k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top ),
% 2.07/1.03      inference(superposition,[status(thm)],[c_2479,c_2468]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_1,plain,
% 2.07/1.03      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 2.07/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2471,plain,
% 2.07/1.03      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 2.07/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2717,plain,
% 2.07/1.03      ( k2_xboole_0(sK7,k1_zfmisc_1(k2_struct_0(sK6))) = k1_zfmisc_1(k2_struct_0(sK6)) ),
% 2.07/1.03      inference(superposition,[status(thm)],[c_2713,c_2471]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_0,plain,
% 2.07/1.03      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 2.07/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2472,plain,
% 2.07/1.03      ( r1_tarski(X0,X1) = iProver_top
% 2.07/1.03      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 2.07/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_3240,plain,
% 2.07/1.03      ( r1_tarski(k1_zfmisc_1(k2_struct_0(sK6)),X0) != iProver_top
% 2.07/1.03      | r1_tarski(sK7,X0) = iProver_top ),
% 2.07/1.03      inference(superposition,[status(thm)],[c_2717,c_2472]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_4825,plain,
% 2.07/1.03      ( r1_tarski(k2_struct_0(sK6),X0) != iProver_top
% 2.07/1.03      | r1_tarski(sK7,k1_zfmisc_1(X0)) = iProver_top ),
% 2.07/1.03      inference(superposition,[status(thm)],[c_2470,c_3240]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_4900,plain,
% 2.07/1.03      ( sP0(sK6,X0) != iProver_top
% 2.07/1.03      | r1_tarski(sK7,k1_zfmisc_1(k2_struct_0(X0))) = iProver_top ),
% 2.07/1.03      inference(superposition,[status(thm)],[c_2458,c_4825]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_4902,plain,
% 2.07/1.03      ( sP0(sK6,sK5) != iProver_top
% 2.07/1.03      | r1_tarski(sK7,k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top ),
% 2.07/1.03      inference(instantiation,[status(thm)],[c_4900]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_3,plain,
% 2.07/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.07/1.03      inference(cnf_transformation,[],[f39]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2469,plain,
% 2.07/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.07/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 2.07/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_21,negated_conjecture,
% 2.07/1.03      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 2.07/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2457,plain,
% 2.07/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
% 2.07/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_422,plain,
% 2.07/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK5 != X0 ),
% 2.07/1.03      inference(resolution_lifted,[status(thm)],[c_336,c_24]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_423,plain,
% 2.07/1.03      ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
% 2.07/1.03      inference(unflattening,[status(thm)],[c_422]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2482,plain,
% 2.07/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK5)))) != iProver_top ),
% 2.07/1.03      inference(light_normalisation,[status(thm)],[c_2457,c_423]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_2838,plain,
% 2.07/1.03      ( r1_tarski(sK7,k1_zfmisc_1(k2_struct_0(sK5))) != iProver_top ),
% 2.07/1.03      inference(superposition,[status(thm)],[c_2469,c_2482]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_18,plain,
% 2.07/1.03      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 2.07/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_7,plain,
% 2.07/1.03      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 2.07/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_350,plain,
% 2.07/1.03      ( sP0(X0,X1)
% 2.07/1.03      | ~ m1_pre_topc(X0,X1)
% 2.07/1.03      | ~ l1_pre_topc(X0)
% 2.07/1.03      | ~ l1_pre_topc(X1) ),
% 2.07/1.03      inference(resolution,[status(thm)],[c_18,c_7]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_354,plain,
% 2.07/1.03      ( ~ m1_pre_topc(X0,X1) | sP0(X0,X1) | ~ l1_pre_topc(X1) ),
% 2.07/1.03      inference(global_propositional_subsumption,
% 2.07/1.03                [status(thm)],
% 2.07/1.03                [c_350,c_20]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_355,plain,
% 2.07/1.03      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 2.07/1.03      inference(renaming,[status(thm)],[c_354]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_396,plain,
% 2.07/1.03      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK6 != X0 | sK5 != X1 ),
% 2.07/1.03      inference(resolution_lifted,[status(thm)],[c_355,c_23]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_397,plain,
% 2.07/1.03      ( sP0(sK6,sK5) | ~ l1_pre_topc(sK5) ),
% 2.07/1.03      inference(unflattening,[status(thm)],[c_396]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_398,plain,
% 2.07/1.03      ( sP0(sK6,sK5) = iProver_top | l1_pre_topc(sK5) != iProver_top ),
% 2.07/1.03      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(c_25,plain,
% 2.07/1.03      ( l1_pre_topc(sK5) = iProver_top ),
% 2.07/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.07/1.03  
% 2.07/1.03  cnf(contradiction,plain,
% 2.07/1.03      ( $false ),
% 2.07/1.03      inference(minisat,[status(thm)],[c_4902,c_2838,c_398,c_25]) ).
% 2.07/1.03  
% 2.07/1.03  
% 2.07/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.07/1.03  
% 2.07/1.03  ------                               Statistics
% 2.07/1.03  
% 2.07/1.03  ------ General
% 2.07/1.03  
% 2.07/1.03  abstr_ref_over_cycles:                  0
% 2.07/1.03  abstr_ref_under_cycles:                 0
% 2.07/1.03  gc_basic_clause_elim:                   0
% 2.07/1.03  forced_gc_time:                         0
% 2.07/1.03  parsing_time:                           0.012
% 2.07/1.03  unif_index_cands_time:                  0.
% 2.07/1.03  unif_index_add_time:                    0.
% 2.07/1.03  orderings_time:                         0.
% 2.07/1.03  out_proof_time:                         0.008
% 2.07/1.03  total_time:                             0.131
% 2.07/1.03  num_of_symbols:                         51
% 2.07/1.03  num_of_terms:                           2853
% 2.07/1.03  
% 2.07/1.03  ------ Preprocessing
% 2.07/1.03  
% 2.07/1.03  num_of_splits:                          0
% 2.07/1.03  num_of_split_atoms:                     0
% 2.07/1.03  num_of_reused_defs:                     0
% 2.07/1.03  num_eq_ax_congr_red:                    36
% 2.07/1.03  num_of_sem_filtered_clauses:            1
% 2.07/1.03  num_of_subtypes:                        0
% 2.07/1.03  monotx_restored_types:                  0
% 2.07/1.03  sat_num_of_epr_types:                   0
% 2.07/1.03  sat_num_of_non_cyclic_types:            0
% 2.07/1.03  sat_guarded_non_collapsed_types:        0
% 2.07/1.03  num_pure_diseq_elim:                    0
% 2.07/1.03  simp_replaced_by:                       0
% 2.07/1.03  res_preprocessed:                       106
% 2.07/1.03  prep_upred:                             0
% 2.07/1.03  prep_unflattend:                        106
% 2.07/1.03  smt_new_axioms:                         0
% 2.07/1.03  pred_elim_cands:                        4
% 2.07/1.03  pred_elim:                              4
% 2.07/1.03  pred_elim_cl:                           5
% 2.07/1.03  pred_elim_cycles:                       6
% 2.07/1.03  merged_defs:                            8
% 2.07/1.03  merged_defs_ncl:                        0
% 2.07/1.03  bin_hyper_res:                          8
% 2.07/1.03  prep_cycles:                            4
% 2.07/1.03  pred_elim_time:                         0.019
% 2.07/1.03  splitting_time:                         0.
% 2.07/1.03  sem_filter_time:                        0.
% 2.07/1.03  monotx_time:                            0.
% 2.07/1.03  subtype_inf_time:                       0.
% 2.07/1.03  
% 2.07/1.03  ------ Problem properties
% 2.07/1.03  
% 2.07/1.03  clauses:                                20
% 2.07/1.03  conjectures:                            2
% 2.07/1.03  epr:                                    1
% 2.07/1.03  horn:                                   16
% 2.07/1.03  ground:                                 5
% 2.07/1.03  unary:                                  5
% 2.07/1.03  binary:                                 6
% 2.07/1.03  lits:                                   55
% 2.07/1.03  lits_eq:                                6
% 2.07/1.03  fd_pure:                                0
% 2.07/1.03  fd_pseudo:                              0
% 2.07/1.03  fd_cond:                                0
% 2.07/1.03  fd_pseudo_cond:                         0
% 2.07/1.03  ac_symbols:                             0
% 2.07/1.03  
% 2.07/1.03  ------ Propositional Solver
% 2.07/1.03  
% 2.07/1.03  prop_solver_calls:                      28
% 2.07/1.03  prop_fast_solver_calls:                 1026
% 2.07/1.03  smt_solver_calls:                       0
% 2.07/1.03  smt_fast_solver_calls:                  0
% 2.07/1.03  prop_num_of_clauses:                    1213
% 2.07/1.03  prop_preprocess_simplified:             4314
% 2.07/1.03  prop_fo_subsumed:                       4
% 2.07/1.03  prop_solver_time:                       0.
% 2.07/1.03  smt_solver_time:                        0.
% 2.07/1.03  smt_fast_solver_time:                   0.
% 2.07/1.03  prop_fast_solver_time:                  0.
% 2.07/1.03  prop_unsat_core_time:                   0.
% 2.07/1.03  
% 2.07/1.03  ------ QBF
% 2.07/1.03  
% 2.07/1.03  qbf_q_res:                              0
% 2.07/1.03  qbf_num_tautologies:                    0
% 2.07/1.03  qbf_prep_cycles:                        0
% 2.07/1.03  
% 2.07/1.03  ------ BMC1
% 2.07/1.03  
% 2.07/1.03  bmc1_current_bound:                     -1
% 2.07/1.03  bmc1_last_solved_bound:                 -1
% 2.07/1.03  bmc1_unsat_core_size:                   -1
% 2.07/1.03  bmc1_unsat_core_parents_size:           -1
% 2.07/1.03  bmc1_merge_next_fun:                    0
% 2.07/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.07/1.03  
% 2.07/1.03  ------ Instantiation
% 2.07/1.03  
% 2.07/1.03  inst_num_of_clauses:                    329
% 2.07/1.03  inst_num_in_passive:                    62
% 2.07/1.03  inst_num_in_active:                     192
% 2.07/1.03  inst_num_in_unprocessed:                75
% 2.07/1.03  inst_num_of_loops:                      200
% 2.07/1.03  inst_num_of_learning_restarts:          0
% 2.07/1.03  inst_num_moves_active_passive:          4
% 2.07/1.03  inst_lit_activity:                      0
% 2.07/1.03  inst_lit_activity_moves:                0
% 2.07/1.03  inst_num_tautologies:                   0
% 2.07/1.03  inst_num_prop_implied:                  0
% 2.07/1.03  inst_num_existing_simplified:           0
% 2.07/1.03  inst_num_eq_res_simplified:             0
% 2.07/1.03  inst_num_child_elim:                    0
% 2.07/1.03  inst_num_of_dismatching_blockings:      30
% 2.07/1.03  inst_num_of_non_proper_insts:           238
% 2.07/1.03  inst_num_of_duplicates:                 0
% 2.07/1.03  inst_inst_num_from_inst_to_res:         0
% 2.07/1.03  inst_dismatching_checking_time:         0.
% 2.07/1.03  
% 2.07/1.03  ------ Resolution
% 2.07/1.03  
% 2.07/1.03  res_num_of_clauses:                     0
% 2.07/1.03  res_num_in_passive:                     0
% 2.07/1.03  res_num_in_active:                      0
% 2.07/1.03  res_num_of_loops:                       110
% 2.07/1.03  res_forward_subset_subsumed:            27
% 2.07/1.03  res_backward_subset_subsumed:           0
% 2.07/1.03  res_forward_subsumed:                   0
% 2.07/1.03  res_backward_subsumed:                  0
% 2.07/1.03  res_forward_subsumption_resolution:     0
% 2.07/1.03  res_backward_subsumption_resolution:    0
% 2.07/1.03  res_clause_to_clause_subsumption:       413
% 2.07/1.03  res_orphan_elimination:                 0
% 2.07/1.03  res_tautology_del:                      64
% 2.07/1.03  res_num_eq_res_simplified:              0
% 2.07/1.03  res_num_sel_changes:                    0
% 2.07/1.03  res_moves_from_active_to_pass:          0
% 2.07/1.03  
% 2.07/1.03  ------ Superposition
% 2.07/1.03  
% 2.07/1.03  sup_time_total:                         0.
% 2.07/1.03  sup_time_generating:                    0.
% 2.07/1.03  sup_time_sim_full:                      0.
% 2.07/1.03  sup_time_sim_immed:                     0.
% 2.07/1.03  
% 2.07/1.03  sup_num_of_clauses:                     88
% 2.07/1.03  sup_num_in_active:                      39
% 2.07/1.03  sup_num_in_passive:                     49
% 2.07/1.03  sup_num_of_loops:                       38
% 2.07/1.03  sup_fw_superposition:                   50
% 2.07/1.03  sup_bw_superposition:                   23
% 2.07/1.03  sup_immediate_simplified:               6
% 2.07/1.03  sup_given_eliminated:                   0
% 2.07/1.03  comparisons_done:                       0
% 2.07/1.03  comparisons_avoided:                    0
% 2.07/1.03  
% 2.07/1.03  ------ Simplifications
% 2.07/1.03  
% 2.07/1.03  
% 2.07/1.03  sim_fw_subset_subsumed:                 0
% 2.07/1.03  sim_bw_subset_subsumed:                 1
% 2.07/1.03  sim_fw_subsumed:                        0
% 2.07/1.03  sim_bw_subsumed:                        0
% 2.07/1.03  sim_fw_subsumption_res:                 1
% 2.07/1.03  sim_bw_subsumption_res:                 0
% 2.07/1.03  sim_tautology_del:                      2
% 2.07/1.03  sim_eq_tautology_del:                   0
% 2.07/1.03  sim_eq_res_simp:                        0
% 2.07/1.03  sim_fw_demodulated:                     0
% 2.07/1.03  sim_bw_demodulated:                     0
% 2.07/1.03  sim_light_normalised:                   8
% 2.07/1.03  sim_joinable_taut:                      0
% 2.07/1.03  sim_joinable_simp:                      0
% 2.07/1.03  sim_ac_normalised:                      0
% 2.07/1.03  sim_smt_subsumption:                    0
% 2.07/1.03  
%------------------------------------------------------------------------------
