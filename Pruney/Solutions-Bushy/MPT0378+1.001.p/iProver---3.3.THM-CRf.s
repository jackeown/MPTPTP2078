%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0378+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 270 expanded)
%              Number of clauses        :   63 (  76 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  625 (1981 expanded)
%              Number of equality atoms :  274 ( 721 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP0(X5,X4,X3,X2,X1,X0,X6) ) ),
    inference(definition_folding,[],[f11,f16])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) )
      & ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f65])).

fof(f27,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7
                & X5 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | X5 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X0 != X7
              & X1 != X7
              & X2 != X7
              & X3 != X7
              & X4 != X7
              & X5 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X0 = X7
            | X1 = X7
            | X2 = X7
            | X3 = X7
            | X4 = X7
            | X5 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6) != X0
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X5 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6) = X0
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X5
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6) != X0
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X5 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6) = X0
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X5
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( X0 = X8
      | X1 = X8
      | X2 = X8
      | X3 = X8
      | X4 = X8
      | X5 = X8
      | ~ r2_hidden(X8,X6)
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
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

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
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

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X0,X1,X2,X3,X4,X8,X6) ) ),
    inference(equality_resolution,[],[f52])).

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
                         => ( k1_xboole_0 != X0
                           => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
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
                           => ( k1_xboole_0 != X0
                             => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
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
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X6,X0) )
     => ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,sK10),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK10,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X6,X0) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,sK9,X6),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X6,X0) )
        & m1_subset_1(sK9,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X6,X0) )
              & m1_subset_1(X5,X0) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,sK8,X5,X6),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
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
                      ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
                      & m1_subset_1(X6,X0) )
                  & m1_subset_1(X5,X0) )
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ m1_subset_1(k4_enumset1(X1,X2,sK7,X4,X5,X6),k1_zfmisc_1(X0))
                    & k1_xboole_0 != X0
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
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ m1_subset_1(k4_enumset1(X1,sK6,X3,X4,X5,X6),k1_zfmisc_1(X0))
                        & k1_xboole_0 != X0
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
                            ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                            & k1_xboole_0 != X0
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
                          ( ~ m1_subset_1(k4_enumset1(sK5,X2,X3,X4,X5,X6),k1_zfmisc_1(sK4))
                          & k1_xboole_0 != sK4
                          & m1_subset_1(X6,sK4) )
                      & m1_subset_1(X5,sK4) )
                  & m1_subset_1(X4,sK4) )
              & m1_subset_1(X3,sK4) )
          & m1_subset_1(X2,sK4) )
      & m1_subset_1(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ m1_subset_1(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4))
    & k1_xboole_0 != sK4
    & m1_subset_1(sK10,sK4)
    & m1_subset_1(sK9,sK4)
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,sK4)
    & m1_subset_1(sK6,sK4)
    & m1_subset_1(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f15,f38,f37,f36,f35,f34,f33])).

fof(f69,plain,(
    m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f45,plain,(
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

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,(
    ~ m1_subset_1(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_26,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k4_enumset1(X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4608,plain,
    ( sP0(X0,X1,sK8,X2,X3,X4,k4_enumset1(X4,X3,X2,sK8,X1,X0)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_12497,plain,
    ( sP0(sK10,sK9,sK8,sK7,sK6,sK5,k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_4608])).

cnf(c_2063,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3170,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,sK4)
    | X1 != sK4
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_10106,plain,
    ( r2_hidden(sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4),sK4)
    | ~ r2_hidden(sK5,sK4)
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) != sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3170])).

cnf(c_3165,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6,sK4)
    | X1 != sK4
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_10056,plain,
    ( r2_hidden(sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4),sK4)
    | ~ r2_hidden(sK6,sK4)
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) != sK6
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3165])).

cnf(c_3160,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK4)
    | X1 != sK4
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_10006,plain,
    ( r2_hidden(sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4),sK4)
    | ~ r2_hidden(sK7,sK4)
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) != sK7
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3160])).

cnf(c_3155,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK8,sK4)
    | X1 != sK4
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_9956,plain,
    ( r2_hidden(sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4),sK4)
    | ~ r2_hidden(sK8,sK4)
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) != sK8
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3155])).

cnf(c_3150,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK9,sK4)
    | X1 != sK4
    | X0 != sK9 ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_9774,plain,
    ( r2_hidden(sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4),sK4)
    | ~ r2_hidden(sK9,sK4)
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) != sK9
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3150])).

cnf(c_3145,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK10,sK4)
    | X1 != sK4
    | X0 != sK10 ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_9724,plain,
    ( r2_hidden(sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4),sK4)
    | ~ r2_hidden(sK10,sK4)
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) != sK10
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3145])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | ~ r2_hidden(X7,X6)
    | X7 = X5
    | X7 = X4
    | X7 = X3
    | X7 = X2
    | X7 = X1
    | X7 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3185,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,k4_enumset1(X5,X4,X3,X2,X1,X0))
    | ~ r2_hidden(X6,k4_enumset1(X5,X4,X3,X2,X1,X0))
    | X6 = X0
    | X6 = X1
    | X6 = X5
    | X6 = X4
    | X6 = X3
    | X6 = X2 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3833,plain,
    ( ~ sP0(X0,X1,sK8,X2,X3,X4,k4_enumset1(X4,X3,X2,sK8,X1,X0))
    | ~ r2_hidden(X5,k4_enumset1(X4,X3,X2,sK8,X1,X0))
    | X5 = X0
    | X5 = X1
    | X5 = X4
    | X5 = X3
    | X5 = X2
    | X5 = sK8 ),
    inference(instantiation,[status(thm)],[c_3185])).

cnf(c_6389,plain,
    ( ~ sP0(sK10,sK9,sK8,sK7,sK6,sK5,k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ r2_hidden(sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4),k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10))
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) = sK10
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) = sK9
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) = sK8
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) = sK7
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) = sK6
    | sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) = sK5 ),
    inference(instantiation,[status(thm)],[c_3833])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3282,plain,
    ( ~ r2_hidden(sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4),sK4)
    | r1_tarski(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3283,plain,
    ( r2_hidden(sK2(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4),k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10))
    | r1_tarski(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3108,plain,
    ( r2_hidden(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4))
    | ~ r1_tarski(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_23,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X5,X6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1765,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | X11 != X12
    | k4_enumset1(X4,X5,X7,X9,X11,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_1766,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(unflattening,[status(thm)],[c_1765])).

cnf(c_1768,plain,
    ( r2_hidden(sK4,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1766])).

cnf(c_1738,plain,
    ( ~ r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X0 = X3
    | X0 = X5
    | X0 = X9
    | X0 = X7
    | X0 = X11
    | X0 = X13
    | k4_enumset1(X2,X4,X6,X8,X10,X12) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_1739,plain,
    ( ~ r2_hidden(X0,k4_enumset1(X1,X2,X3,X4,X5,X6))
    | X0 = X3
    | X0 = X1
    | X0 = X2
    | X0 = X4
    | X0 = X5
    | X0 = X6 ),
    inference(unflattening,[status(thm)],[c_1738])).

cnf(c_1741,plain,
    ( ~ r2_hidden(sK4,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_720,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_36])).

cnf(c_721,plain,
    ( r2_hidden(sK5,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_707,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_35])).

cnf(c_708,plain,
    ( r2_hidden(sK6,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_694,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_695,plain,
    ( r2_hidden(sK7,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_681,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_33])).

cnf(c_682,plain,
    ( r2_hidden(sK8,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_668,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_32])).

cnf(c_669,plain,
    ( r2_hidden(sK9,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_646,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_31])).

cnf(c_647,plain,
    ( r2_hidden(sK10,sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_209,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_28])).

cnf(c_210,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_209])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_629,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10) != X0
    | k1_zfmisc_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_210,c_29])).

cnf(c_630,plain,
    ( ~ r2_hidden(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_27,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_48,plain,
    ( ~ v1_xboole_0(sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12497,c_10106,c_10056,c_10006,c_9956,c_9774,c_9724,c_6389,c_3282,c_3283,c_3108,c_1768,c_1741,c_721,c_708,c_695,c_682,c_669,c_647,c_630,c_48,c_30])).


%------------------------------------------------------------------------------
