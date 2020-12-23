%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0376+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:09 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_434)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f9,f16])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f52])).

fof(f22,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4) != X0
            & sK2(X0,X1,X2,X3,X4) != X1
            & sK2(X0,X1,X2,X3,X4) != X2
            & sK2(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
        & ( sK2(X0,X1,X2,X3,X4) = X0
          | sK2(X0,X1,X2,X3,X4) = X1
          | sK2(X0,X1,X2,X3,X4) = X2
          | sK2(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK2(X0,X1,X2,X3,X4) != X0
              & sK2(X0,X1,X2,X3,X4) != X1
              & sK2(X0,X1,X2,X3,X4) != X2
              & sK2(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
          & ( sK2(X0,X1,X2,X3,X4) = X0
            | sK2(X0,X1,X2,X3,X4) = X1
            | sK2(X0,X1,X2,X3,X4) = X2
            | sK2(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X0 = X6
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | ~ r2_hidden(X6,X4)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k1_xboole_0 != X0
                   => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( k1_xboole_0 != X0
                     => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X4,X0) )
     => ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,sK8),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( ~ m1_subset_1(k2_enumset1(X1,X2,sK7,X4),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X4,X0) )
        & m1_subset_1(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_subset_1(k2_enumset1(X1,sK6,X3,X4),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
                & m1_subset_1(X4,X0) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                    & k1_xboole_0 != X0
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(sK5,X2,X3,X4),k1_zfmisc_1(sK4))
                  & k1_xboole_0 != sK4
                  & m1_subset_1(X4,sK4) )
              & m1_subset_1(X3,sK4) )
          & m1_subset_1(X2,sK4) )
      & m1_subset_1(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ m1_subset_1(k2_enumset1(sK5,sK6,sK7,sK8),k1_zfmisc_1(sK4))
    & k1_xboole_0 != sK4
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,sK4)
    & m1_subset_1(sK6,sK4)
    & m1_subset_1(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f15,f36,f35,f34,f33])).

fof(f68,plain,(
    ~ m1_subset_1(k2_enumset1(sK5,sK6,sK7,sK8),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_21,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1967,plain,
    ( r2_hidden(sK3(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1969,plain,
    ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ r2_hidden(X5,X4)
    | X5 = X3
    | X5 = X2
    | X5 = X1
    | X5 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1971,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | X0 = X4
    | sP0(X4,X3,X1,X2,X5) != iProver_top
    | r2_hidden(X0,X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5403,plain,
    ( X0 = X1
    | X2 = X1
    | X3 = X1
    | X4 = X1
    | r2_hidden(X1,k2_enumset1(X0,X4,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1969,c_1971])).

cnf(c_6802,plain,
    ( sK3(k2_enumset1(X0,X1,X2,X3),X4) = X0
    | sK3(k2_enumset1(X0,X1,X2,X3),X4) = X2
    | sK3(k2_enumset1(X0,X1,X2,X3),X4) = X3
    | sK3(k2_enumset1(X0,X1,X2,X3),X4) = X1
    | r1_tarski(k2_enumset1(X0,X1,X2,X3),X4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_5403])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1982,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_18,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_167,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_24])).

cnf(c_168,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_167])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(k2_enumset1(sK5,sK6,sK7,sK8),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_393,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_enumset1(sK5,sK6,sK7,sK8) != X0
    | k1_zfmisc_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_168,c_25])).

cnf(c_394,plain,
    ( ~ r2_hidden(k2_enumset1(sK5,sK6,sK7,sK8),k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_1963,plain,
    ( r2_hidden(k2_enumset1(sK5,sK6,sK7,sK8),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_3006,plain,
    ( r1_tarski(k2_enumset1(sK5,sK6,sK7,sK8),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1982,c_1963])).

cnf(c_15762,plain,
    ( sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK8
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK7
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK6
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_6802,c_3006])).

cnf(c_20,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1968,plain,
    ( r2_hidden(sK3(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18387,plain,
    ( sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK7
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK6
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK5
    | r2_hidden(sK8,sK4) != iProver_top
    | r1_tarski(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_15762,c_1968])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_40,plain,
    ( ~ v1_xboole_0(sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_410,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_411,plain,
    ( r2_hidden(sK8,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_2189,plain,
    ( r2_hidden(k2_enumset1(sK5,sK6,sK7,sK8),k1_zfmisc_1(sK4))
    | ~ r1_tarski(k2_enumset1(sK5,sK6,sK7,sK8),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_18425,plain,
    ( ~ r2_hidden(sK8,sK4)
    | r1_tarski(k2_enumset1(sK5,sK6,sK7,sK8),sK4)
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK7
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK6
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18387])).

cnf(c_18515,plain,
    ( sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK7
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK6
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18387,c_26,c_40,c_394,c_411,c_2189,c_18425])).

cnf(c_18523,plain,
    ( sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK6
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK5
    | r2_hidden(sK7,sK4) != iProver_top
    | r1_tarski(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_18515,c_1968])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_432,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_433,plain,
    ( r2_hidden(sK7,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_18556,plain,
    ( ~ r2_hidden(sK7,sK4)
    | r1_tarski(k2_enumset1(sK5,sK6,sK7,sK8),sK4)
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK6
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18523])).

cnf(c_18558,plain,
    ( sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK6
    | sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18523,c_26,c_41,c_395,c_434,c_2190])).

cnf(c_18566,plain,
    ( sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK5
    | r2_hidden(sK6,sK4) != iProver_top
    | r1_tarski(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_18558,c_1968])).

cnf(c_39,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41,plain,
    ( k1_xboole_0 = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_395,plain,
    ( r2_hidden(k2_enumset1(sK5,sK6,sK7,sK8),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_445,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_446,plain,
    ( r2_hidden(sK6,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_447,plain,
    ( r2_hidden(sK6,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_2190,plain,
    ( r2_hidden(k2_enumset1(sK5,sK6,sK7,sK8),k1_zfmisc_1(sK4)) = iProver_top
    | r1_tarski(k2_enumset1(sK5,sK6,sK7,sK8),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2189])).

cnf(c_18667,plain,
    ( sK3(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18566,c_26,c_41,c_395,c_447,c_2190])).

cnf(c_18675,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | r1_tarski(k2_enumset1(sK5,sK6,sK7,sK8),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_18667,c_1968])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_458,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_459,plain,
    ( r2_hidden(sK5,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_460,plain,
    ( r2_hidden(sK5,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18675,c_2190,c_460,c_395,c_41,c_26])).


%------------------------------------------------------------------------------
