%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0377+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_24175)

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

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f10,f16])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f59])).

fof(f23,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4,X5) != X0
            & sK2(X0,X1,X2,X3,X4,X5) != X1
            & sK2(X0,X1,X2,X3,X4,X5) != X2
            & sK2(X0,X1,X2,X3,X4,X5) != X3
            & sK2(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK2(X0,X1,X2,X3,X4,X5) = X0
          | sK2(X0,X1,X2,X3,X4,X5) = X1
          | sK2(X0,X1,X2,X3,X4,X5) = X2
          | sK2(X0,X1,X2,X3,X4,X5) = X3
          | sK2(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK2(X0,X1,X2,X3,X4,X5) != X0
              & sK2(X0,X1,X2,X3,X4,X5) != X1
              & sK2(X0,X1,X2,X3,X4,X5) != X2
              & sK2(X0,X1,X2,X3,X4,X5) != X3
              & sK2(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK2(X0,X1,X2,X3,X4,X5) = X0
            | sK2(X0,X1,X2,X3,X4,X5) = X1
            | sK2(X0,X1,X2,X3,X4,X5) = X2
            | sK2(X0,X1,X2,X3,X4,X5) = X3
            | sK2(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f47,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( X0 = X7
      | X1 = X7
      | X2 = X7
      | X3 = X7
      | X4 = X7
      | ~ r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f65,plain,(
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
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ( k1_xboole_0 != X0
                       => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
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
                   => ! [X5] :
                        ( m1_subset_1(X5,X0)
                       => ( k1_xboole_0 != X0
                         => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
                      & m1_subset_1(X5,X0) )
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
                  ( ? [X5] :
                      ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X5,X0) )
     => ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,sK9),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK9,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X5,X0) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,sK8,X5),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X5,X0) )
        & m1_subset_1(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X5,X0) )
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ m1_subset_1(k3_enumset1(X1,X2,sK7,X4,X5),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
                & m1_subset_1(X5,X0) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ m1_subset_1(k3_enumset1(X1,sK6,X3,X4,X5),k1_zfmisc_1(X0))
                    & k1_xboole_0 != X0
                    & m1_subset_1(X5,X0) )
                & m1_subset_1(X4,X0) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                        & k1_xboole_0 != X0
                        & m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ m1_subset_1(k3_enumset1(sK5,X2,X3,X4,X5),k1_zfmisc_1(sK4))
                      & k1_xboole_0 != sK4
                      & m1_subset_1(X5,sK4) )
                  & m1_subset_1(X4,sK4) )
              & m1_subset_1(X3,sK4) )
          & m1_subset_1(X2,sK4) )
      & m1_subset_1(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4))
    & k1_xboole_0 != sK4
    & m1_subset_1(sK9,sK4)
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,sK4)
    & m1_subset_1(sK6,sK4)
    & m1_subset_1(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f15,f37,f36,f35,f34,f33])).

fof(f72,plain,(
    ~ m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f38])).

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

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23898,plain,
    ( r2_hidden(sK3(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,plain,
    ( sP0(X0,X1,X2,X3,X4,k3_enumset1(X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_23900,plain,
    ( sP0(X0,X1,X2,X3,X4,k3_enumset1(X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | ~ r2_hidden(X6,X5)
    | X6 = X4
    | X6 = X3
    | X6 = X2
    | X6 = X1
    | X6 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23901,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | X0 = X4
    | X0 = X5
    | sP0(X5,X4,X2,X3,X1,X6) != iProver_top
    | r2_hidden(X0,X6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_25406,plain,
    ( X0 = X1
    | X2 = X1
    | X3 = X1
    | X4 = X1
    | X5 = X1
    | r2_hidden(X1,k3_enumset1(X2,X3,X0,X4,X5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23900,c_23901])).

cnf(c_27127,plain,
    ( sK3(k3_enumset1(X0,X1,X2,X3,X4),X5) = X0
    | sK3(k3_enumset1(X0,X1,X2,X3,X4),X5) = X1
    | sK3(k3_enumset1(X0,X1,X2,X3,X4),X5) = X2
    | sK3(k3_enumset1(X0,X1,X2,X3,X4),X5) = X3
    | sK3(k3_enumset1(X0,X1,X2,X3,X4),X5) = X4
    | r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),X5) = iProver_top ),
    inference(superposition,[status(thm)],[c_23898,c_25406])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_23904,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_26])).

cnf(c_300,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_299])).

cnf(c_23889,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_24482,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_23904,c_23889])).

cnf(c_27,negated_conjecture,
    ( ~ m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23895,plain,
    ( m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26194,plain,
    ( r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_24482,c_23895])).

cnf(c_27430,plain,
    ( sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK9
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK8
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK7
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK6
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_27127,c_26194])).

cnf(c_22,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23899,plain,
    ( r2_hidden(sK3(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_27650,plain,
    ( sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK8
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK7
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK6
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5
    | r2_hidden(sK9,sK4) != iProver_top
    | r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_27430,c_23899])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_44,plain,
    ( ~ v1_xboole_0(sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3678,plain,
    ( m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4))
    | ~ r2_hidden(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_5846,plain,
    ( r2_hidden(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4))
    | ~ r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24172,plain,
    ( r2_hidden(sK9,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[status(thm)],[c_7,c_29])).

cnf(c_27719,plain,
    ( ~ r2_hidden(sK9,sK4)
    | r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4)
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK8
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK7
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK6
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_27650])).

cnf(c_27935,plain,
    ( sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK8
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK7
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK6
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27650,c_28,c_27,c_44,c_3678,c_5846,c_24172,c_27719])).

cnf(c_27945,plain,
    ( sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK7
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK6
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5
    | r2_hidden(sK8,sK4) != iProver_top
    | r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_27935,c_23899])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24174,plain,
    ( r2_hidden(sK8,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[status(thm)],[c_7,c_30])).

cnf(c_28005,plain,
    ( ~ r2_hidden(sK8,sK4)
    | r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4)
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK7
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK6
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_27945])).

cnf(c_28008,plain,
    ( sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK7
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK6
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27945,c_28,c_39,c_45,c_3679,c_5847,c_24175])).

cnf(c_28018,plain,
    ( sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK6
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5
    | r2_hidden(sK7,sK4) != iProver_top
    | r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_28008,c_23899])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24176,plain,
    ( r2_hidden(sK7,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[status(thm)],[c_7,c_31])).

cnf(c_28069,plain,
    ( ~ r2_hidden(sK7,sK4)
    | r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4)
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK6
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_28018])).

cnf(c_28332,plain,
    ( sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK6
    | sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28018,c_28,c_39,c_45,c_3679,c_5847,c_24177])).

cnf(c_28342,plain,
    ( sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5
    | r2_hidden(sK6,sK4) != iProver_top
    | r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_28332,c_23899])).

cnf(c_39,plain,
    ( m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_43,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_45,plain,
    ( k1_xboole_0 = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_3679,plain,
    ( m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4)) = iProver_top
    | r2_hidden(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3678])).

cnf(c_5847,plain,
    ( r2_hidden(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK4)) = iProver_top
    | r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5846])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24178,plain,
    ( r2_hidden(sK6,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[status(thm)],[c_7,c_32])).

cnf(c_24179,plain,
    ( r2_hidden(sK6,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24178])).

cnf(c_28387,plain,
    ( sK3(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28342,c_28,c_39,c_45,c_3679,c_5847,c_24179])).

cnf(c_28397,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_28387,c_23899])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24180,plain,
    ( r2_hidden(sK5,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[status(thm)],[c_7,c_33])).

cnf(c_24181,plain,
    ( r2_hidden(sK5,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24180])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28397,c_24181,c_5847,c_3679,c_45,c_39,c_28])).


%------------------------------------------------------------------------------
