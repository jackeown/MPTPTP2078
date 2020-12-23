%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0380+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 31.89s
% Output     : CNFRefutation 31.89s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_822)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f11,f17,f16])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f69])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X10,X8)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f32,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f33])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

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

fof(f23,plain,(
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

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f72,plain,(
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
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ! [X7] :
                              ( m1_subset_1(X7,X0)
                             => ! [X8] :
                                  ( m1_subset_1(X8,X0)
                                 => ( k1_xboole_0 != X0
                                   => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
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
                       => ! [X6] :
                            ( m1_subset_1(X6,X0)
                           => ! [X7] :
                                ( m1_subset_1(X7,X0)
                               => ! [X8] :
                                    ( m1_subset_1(X8,X0)
                                   => ( k1_xboole_0 != X0
                                     => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  & k1_xboole_0 != X0
                                  & m1_subset_1(X8,X0) )
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
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
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  & k1_xboole_0 != X0
                                  & m1_subset_1(X8,X0) )
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ? [X8] :
          ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X8,X0) )
     => ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,sK13),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK13,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ? [X8] :
              ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X8,X0) )
          & m1_subset_1(X7,X0) )
     => ( ? [X8] :
            ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,sK12,X8),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X8,X0) )
        & m1_subset_1(sK12,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X8,X0) )
              & m1_subset_1(X7,X0) )
          & m1_subset_1(X6,X0) )
     => ( ? [X7] :
            ( ? [X8] :
                ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,sK11,X7,X8),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
                & m1_subset_1(X8,X0) )
            & m1_subset_1(X7,X0) )
        & m1_subset_1(sK11,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
                      & m1_subset_1(X8,X0) )
                  & m1_subset_1(X7,X0) )
              & m1_subset_1(X6,X0) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,sK10,X6,X7,X8),k1_zfmisc_1(X0))
                    & k1_xboole_0 != X0
                    & m1_subset_1(X8,X0) )
                & m1_subset_1(X7,X0) )
            & m1_subset_1(X6,X0) )
        & m1_subset_1(sK10,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X8,X0) )
                      & m1_subset_1(X7,X0) )
                  & m1_subset_1(X6,X0) )
              & m1_subset_1(X5,X0) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ? [X8] :
                        ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,sK9,X5,X6,X7,X8),k1_zfmisc_1(X0))
                        & k1_xboole_0 != X0
                        & m1_subset_1(X8,X0) )
                    & m1_subset_1(X7,X0) )
                & m1_subset_1(X6,X0) )
            & m1_subset_1(X5,X0) )
        & m1_subset_1(sK9,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ? [X8] :
                              ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
                              & m1_subset_1(X8,X0) )
                          & m1_subset_1(X7,X0) )
                      & m1_subset_1(X6,X0) )
                  & m1_subset_1(X5,X0) )
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ? [X8] :
                            ( ~ m1_subset_1(k6_enumset1(X1,X2,sK8,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                            & k1_xboole_0 != X0
                            & m1_subset_1(X8,X0) )
                        & m1_subset_1(X7,X0) )
                    & m1_subset_1(X6,X0) )
                & m1_subset_1(X5,X0) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  & k1_xboole_0 != X0
                                  & m1_subset_1(X8,X0) )
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ? [X8] :
                                ( ~ m1_subset_1(k6_enumset1(X1,sK7,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                & k1_xboole_0 != X0
                                & m1_subset_1(X8,X0) )
                            & m1_subset_1(X7,X0) )
                        & m1_subset_1(X6,X0) )
                    & m1_subset_1(X5,X0) )
                & m1_subset_1(X4,X0) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ? [X8] :
                                    ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                    & k1_xboole_0 != X0
                                    & m1_subset_1(X8,X0) )
                                & m1_subset_1(X7,X0) )
                            & m1_subset_1(X6,X0) )
                        & m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(sK6,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(sK5))
                                  & k1_xboole_0 != sK5
                                  & m1_subset_1(X8,sK5) )
                              & m1_subset_1(X7,sK5) )
                          & m1_subset_1(X6,sK5) )
                      & m1_subset_1(X5,sK5) )
                  & m1_subset_1(X4,sK5) )
              & m1_subset_1(X3,sK5) )
          & m1_subset_1(X2,sK5) )
      & m1_subset_1(sK6,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ m1_subset_1(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),k1_zfmisc_1(sK5))
    & k1_xboole_0 != sK5
    & m1_subset_1(sK13,sK5)
    & m1_subset_1(sK12,sK5)
    & m1_subset_1(sK11,sK5)
    & m1_subset_1(sK10,sK5)
    & m1_subset_1(sK9,sK5)
    & m1_subset_1(sK8,sK5)
    & m1_subset_1(sK7,sK5)
    & m1_subset_1(sK6,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13])],[f15,f43,f42,f41,f40,f39,f38,f37,f36])).

fof(f82,plain,(
    ~ m1_subset_1(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f44])).

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

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    m1_subset_1(sK13,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    m1_subset_1(sK12,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    m1_subset_1(sK11,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    m1_subset_1(sK10,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    m1_subset_1(sK8,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    m1_subset_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    m1_subset_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2453,plain,
    ( r2_hidden(sK3(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_25,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2437,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | ~ r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2448,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) = iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3148,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) = iProver_top
    | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_2448])).

cnf(c_3687,plain,
    ( sP0(sK3(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8),X7,X6,X5,X4,X3,X2,X1,X0) = iProver_top
    | r1_tarski(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2453,c_3148])).

cnf(c_23,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X3 = X0
    | X2 = X0
    | X1 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2439,plain,
    ( X0 = X1
    | X2 = X1
    | X3 = X1
    | X4 = X1
    | X5 = X1
    | X6 = X1
    | X7 = X1
    | X8 = X1
    | sP0(X1,X8,X6,X7,X5,X4,X3,X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4181,plain,
    ( sK3(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8) = X0
    | sK3(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8) = X1
    | sK3(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8) = X2
    | sK3(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8) = X3
    | sK3(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8) = X4
    | sK3(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8) = X6
    | sK3(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8) = X5
    | sK3(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8) = X7
    | r1_tarski(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_3687,c_2439])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2456,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_216,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_27])).

cnf(c_217,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_28,negated_conjecture,
    ( ~ m1_subset_1(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_781,plain,
    ( ~ r2_hidden(X0,X1)
    | k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13) != X0
    | k1_zfmisc_1(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_217,c_28])).

cnf(c_782,plain,
    ( ~ r2_hidden(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),k1_zfmisc_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_2432,plain,
    ( r2_hidden(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),k1_zfmisc_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_2845,plain,
    ( r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2456,c_2432])).

cnf(c_130580,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK13
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK12
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK11
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK10
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(superposition,[status(thm)],[c_4181,c_2845])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2454,plain,
    ( r2_hidden(sK3(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_135671,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK12
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK11
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK10
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6
    | r2_hidden(sK13,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_130580,c_2454])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_51,plain,
    ( ~ v1_xboole_0(sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK13,sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_798,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_30])).

cnf(c_799,plain,
    ( r2_hidden(sK13,sK5)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_798])).

cnf(c_2848,plain,
    ( ~ r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2845])).

cnf(c_135776,plain,
    ( ~ r2_hidden(sK13,sK5)
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5)
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK12
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK11
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK10
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_135671])).

cnf(c_135778,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK12
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK11
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK10
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_135671,c_29,c_51,c_799,c_2848,c_135776])).

cnf(c_135792,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK11
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK10
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6
    | r2_hidden(sK12,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_135778,c_2454])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK12,sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_820,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_31])).

cnf(c_821,plain,
    ( r2_hidden(sK12,sK5)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_135888,plain,
    ( ~ r2_hidden(sK12,sK5)
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5)
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK11
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK10
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_135792])).

cnf(c_135890,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK11
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK10
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_135792,c_29,c_52,c_822,c_2845])).

cnf(c_135904,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK10
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6
    | r2_hidden(sK11,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_135890,c_2454])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK11,sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_833,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_32])).

cnf(c_834,plain,
    ( r2_hidden(sK11,sK5)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_833])).

cnf(c_135991,plain,
    ( ~ r2_hidden(sK11,sK5)
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5)
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK10
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_135904])).

cnf(c_135993,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK10
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_135904,c_29,c_52,c_835,c_2845])).

cnf(c_136007,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6
    | r2_hidden(sK10,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_135993,c_2454])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK10,sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_846,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_33])).

cnf(c_847,plain,
    ( r2_hidden(sK10,sK5)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_846])).

cnf(c_136085,plain,
    ( ~ r2_hidden(sK10,sK5)
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5)
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_136007])).

cnf(c_140649,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK9
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_136007,c_29,c_52,c_848,c_2845])).

cnf(c_140663,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6
    | r2_hidden(sK9,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_140649,c_2454])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_859,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_860,plain,
    ( r2_hidden(sK9,sK5)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_140732,plain,
    ( ~ r2_hidden(sK9,sK5)
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5)
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_140663])).

cnf(c_140737,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK8
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_140663,c_29,c_52,c_861,c_2845])).

cnf(c_140751,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6
    | r2_hidden(sK8,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_140737,c_2454])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK8,sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_872,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_35])).

cnf(c_873,plain,
    ( r2_hidden(sK8,sK5)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_140811,plain,
    ( ~ r2_hidden(sK8,sK5)
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5)
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_140751])).

cnf(c_143900,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK7
    | sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_140751,c_29,c_52,c_874,c_2845])).

cnf(c_143914,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6
    | r2_hidden(sK7,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_143900,c_2454])).

cnf(c_50,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_52,plain,
    ( k1_xboole_0 = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_885,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_36])).

cnf(c_886,plain,
    ( r2_hidden(sK7,sK5)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_885])).

cnf(c_887,plain,
    ( r2_hidden(sK7,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_143967,plain,
    ( sK3(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_143914,c_29,c_52,c_887,c_2845])).

cnf(c_143981,plain,
    ( r2_hidden(sK6,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK7,sK8,sK9,sK10,sK11,sK12,sK13),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_143967,c_2454])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_898,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_37])).

cnf(c_899,plain,
    ( r2_hidden(sK6,sK5)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_900,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_899])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143981,c_2845,c_900,c_52,c_29])).


%------------------------------------------------------------------------------
