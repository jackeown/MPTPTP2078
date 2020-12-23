%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0379+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:09 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 302 expanded)
%              Number of clauses        :   68 (  83 expanded)
%              Number of leaves         :   19 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :  696 (2425 expanded)
%              Number of equality atoms :  314 ( 847 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ),
    inference(definition_folding,[],[f11,f16])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) )
      & ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP0(X6,X5,X4,X3,X2,X1,X0,k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(equality_resolution,[],[f68])).

fof(f27,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8
                & X6 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | X6 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9 ) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ( X0 != X8
              & X1 != X8
              & X2 != X8
              & X3 != X8
              & X4 != X8
              & X5 != X8
              & X6 != X8 )
            | ~ r2_hidden(X8,X7) )
          & ( X0 = X8
            | X1 = X8
            | X2 = X8
            | X3 = X8
            | X4 = X8
            | X5 = X8
            | X6 = X8
            | r2_hidden(X8,X7) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X0
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X5
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X6 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X0
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X5
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X6
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X0
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X5
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7) != X6 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X0
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X5
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7) = X6
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9 ) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( X0 = X9
      | X1 = X9
      | X2 = X9
      | X3 = X9
      | X4 = X9
      | X5 = X9
      | X6 = X9
      | ~ r2_hidden(X9,X7)
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
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

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | X6 != X9
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | ~ sP0(X0,X1,X2,X3,X4,X5,X9,X7) ) ),
    inference(equality_resolution,[],[f53])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
                             => ( k1_xboole_0 != X0
                               => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
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
                               => ( k1_xboole_0 != X0
                                 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
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
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X7,X0) )
     => ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,sK11),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK11,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X7,X0) )
          & m1_subset_1(X6,X0) )
     => ( ? [X7] :
            ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,sK10,X7),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X7,X0) )
        & m1_subset_1(sK10,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X7,X0) )
              & m1_subset_1(X6,X0) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,sK9,X6,X7),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
                & m1_subset_1(X7,X0) )
            & m1_subset_1(X6,X0) )
        & m1_subset_1(sK9,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
                      & m1_subset_1(X7,X0) )
                  & m1_subset_1(X6,X0) )
              & m1_subset_1(X5,X0) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,sK8,X5,X6,X7),k1_zfmisc_1(X0))
                    & k1_xboole_0 != X0
                    & m1_subset_1(X7,X0) )
                & m1_subset_1(X6,X0) )
            & m1_subset_1(X5,X0) )
        & m1_subset_1(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X7,X0) )
                      & m1_subset_1(X6,X0) )
                  & m1_subset_1(X5,X0) )
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ~ m1_subset_1(k5_enumset1(X1,X2,sK7,X4,X5,X6,X7),k1_zfmisc_1(X0))
                        & k1_xboole_0 != X0
                        & m1_subset_1(X7,X0) )
                    & m1_subset_1(X6,X0) )
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
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
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
                            ( ~ m1_subset_1(k5_enumset1(X1,sK6,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                            & k1_xboole_0 != X0
                            & m1_subset_1(X7,X0) )
                        & m1_subset_1(X6,X0) )
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
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                                & k1_xboole_0 != X0
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
                              ( ~ m1_subset_1(k5_enumset1(sK5,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK4))
                              & k1_xboole_0 != sK4
                              & m1_subset_1(X7,sK4) )
                          & m1_subset_1(X6,sK4) )
                      & m1_subset_1(X5,sK4) )
                  & m1_subset_1(X4,sK4) )
              & m1_subset_1(X3,sK4) )
          & m1_subset_1(X2,sK4) )
      & m1_subset_1(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4))
    & k1_xboole_0 != sK4
    & m1_subset_1(sK11,sK4)
    & m1_subset_1(sK10,sK4)
    & m1_subset_1(sK9,sK4)
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,sK4)
    & m1_subset_1(sK6,sK4)
    & m1_subset_1(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f15,f39,f38,f37,f36,f35,f34,f33])).

fof(f72,plain,(
    m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    m1_subset_1(sK11,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f46,plain,(
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

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,(
    ~ m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_28,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X6,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5173,plain,
    ( sP0(X0,X1,sK9,X2,X3,X4,X5,k5_enumset1(X5,X4,X3,X2,sK9,X1,X0)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_13601,plain,
    ( sP0(sK11,sK10,sK9,sK8,sK7,sK6,sK5,k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_5173])).

cnf(c_2482,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3686,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,sK4)
    | X1 != sK4
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_11082,plain,
    ( r2_hidden(sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4),sK4)
    | ~ r2_hidden(sK5,sK4)
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) != sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3686])).

cnf(c_3681,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6,sK4)
    | X1 != sK4
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_10951,plain,
    ( r2_hidden(sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4),sK4)
    | ~ r2_hidden(sK6,sK4)
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) != sK6
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3681])).

cnf(c_3676,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK4)
    | X1 != sK4
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_10896,plain,
    ( r2_hidden(sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4),sK4)
    | ~ r2_hidden(sK7,sK4)
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) != sK7
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3676])).

cnf(c_3671,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK8,sK4)
    | X1 != sK4
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_10841,plain,
    ( r2_hidden(sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4),sK4)
    | ~ r2_hidden(sK8,sK4)
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) != sK8
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3671])).

cnf(c_3666,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK9,sK4)
    | X1 != sK4
    | X0 != sK9 ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_10786,plain,
    ( r2_hidden(sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4),sK4)
    | ~ r2_hidden(sK9,sK4)
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) != sK9
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3666])).

cnf(c_3661,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK10,sK4)
    | X1 != sK4
    | X0 != sK10 ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_10731,plain,
    ( r2_hidden(sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4),sK4)
    | ~ r2_hidden(sK10,sK4)
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) != sK10
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3661])).

cnf(c_3656,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK11,sK4)
    | X1 != sK4
    | X0 != sK11 ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_10628,plain,
    ( r2_hidden(sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4),sK4)
    | ~ r2_hidden(sK11,sK4)
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) != sK11
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3656])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ r2_hidden(X8,X7)
    | X8 = X6
    | X8 = X5
    | X8 = X4
    | X8 = X3
    | X8 = X2
    | X8 = X1
    | X8 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3717,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X6,X5,X4,X3,X2,X1,X0))
    | ~ r2_hidden(X7,k5_enumset1(X6,X5,X4,X3,X2,X1,X0))
    | X7 = X0
    | X7 = X1
    | X7 = X6
    | X7 = X5
    | X7 = X4
    | X7 = X3
    | X7 = X2 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_4353,plain,
    ( ~ sP0(X0,X1,sK9,X2,X3,X4,X5,k5_enumset1(X5,X4,X3,X2,sK9,X1,X0))
    | ~ r2_hidden(X6,k5_enumset1(X5,X4,X3,X2,sK9,X1,X0))
    | X6 = X0
    | X6 = X1
    | X6 = X5
    | X6 = X4
    | X6 = X3
    | X6 = X2
    | X6 = sK9 ),
    inference(instantiation,[status(thm)],[c_3717])).

cnf(c_6818,plain,
    ( ~ sP0(sK11,sK10,sK9,sK8,sK7,sK6,sK5,k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ r2_hidden(sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4),k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11))
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) = sK11
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) = sK10
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) = sK9
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) = sK8
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) = sK7
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) = sK6
    | sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) = sK5 ),
    inference(instantiation,[status(thm)],[c_4353])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3823,plain,
    ( ~ r2_hidden(sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4),sK4)
    | r1_tarski(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3824,plain,
    ( r2_hidden(sK2(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4),k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11))
    | r1_tarski(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3617,plain,
    ( r2_hidden(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4))
    | ~ r1_tarski(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_25,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
    | r2_hidden(X6,X7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2101,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | X11 != X12
    | X13 != X14
    | k5_enumset1(X4,X5,X7,X9,X11,X13,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_28])).

cnf(c_2102,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(unflattening,[status(thm)],[c_2101])).

cnf(c_2104,plain,
    ( r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_2102])).

cnf(c_2071,plain,
    ( ~ r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | X0 = X3
    | X0 = X5
    | X0 = X7
    | X0 = X11
    | X0 = X9
    | X0 = X13
    | X0 = X15
    | k5_enumset1(X2,X4,X6,X8,X10,X12,X14) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_2072,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
    | X0 = X1
    | X0 = X2
    | X0 = X3
    | X0 = X4
    | X0 = X5
    | X0 = X6
    | X0 = X7 ),
    inference(unflattening,[status(thm)],[c_2071])).

cnf(c_2074,plain,
    ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2072])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_766,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_39])).

cnf(c_767,plain,
    ( r2_hidden(sK5,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_753,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_38])).

cnf(c_754,plain,
    ( r2_hidden(sK6,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_740,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_37])).

cnf(c_741,plain,
    ( r2_hidden(sK7,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_727,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_36])).

cnf(c_728,plain,
    ( r2_hidden(sK8,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_714,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_35])).

cnf(c_715,plain,
    ( r2_hidden(sK9,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_701,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_702,plain,
    ( r2_hidden(sK10,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_701])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK11,sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_679,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_33])).

cnf(c_680,plain,
    ( r2_hidden(sK11,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_30])).

cnf(c_225,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_662,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11) != X0
    | k1_zfmisc_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_225,c_31])).

cnf(c_663,plain,
    ( ~ r2_hidden(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_29,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_52,plain,
    ( ~ v1_xboole_0(sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13601,c_11082,c_10951,c_10896,c_10841,c_10786,c_10731,c_10628,c_6818,c_3823,c_3824,c_3617,c_2104,c_2074,c_767,c_754,c_741,c_728,c_715,c_702,c_680,c_663,c_52,c_32])).


%------------------------------------------------------------------------------
