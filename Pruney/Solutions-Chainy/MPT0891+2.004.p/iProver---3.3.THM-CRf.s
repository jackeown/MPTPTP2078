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
% DateTime   : Thu Dec  3 11:58:32 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  184 (44271 expanded)
%              Number of clauses        :   95 (11583 expanded)
%              Number of leaves         :   21 (13207 expanded)
%              Depth                    :   30
%              Number of atoms          :  685 (203329 expanded)
%              Number of equality atoms :  488 (159356 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f103,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f102])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f73,f66,f67])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( k7_mcart_1(X0,X1,X2,sK7) = sK7
          | k6_mcart_1(X0,X1,X2,sK7) = sK7
          | k5_mcart_1(X0,X1,X2,sK7) = sK7 )
        & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK4,sK5,sK6,X3) = X3
            | k6_mcart_1(sK4,sK5,sK6,X3) = X3
            | k5_mcart_1(sK4,sK5,sK6,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK4,sK5,sK6)) )
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( k7_mcart_1(sK4,sK5,sK6,sK7) = sK7
      | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
      | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7 )
    & m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f21,f41,f40])).

fof(f82,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f82,f67])).

fof(f79,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f84,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f84])).

fof(f111,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f84])).

fof(f109,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f87])).

fof(f110,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f109])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f67])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f67])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f75,f67])).

fof(f9,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f112,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7 ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f38])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f71,f66])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f106,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f50])).

fof(f107,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f106])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f62,f62])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f72,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f72,f66])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_977,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_380,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | sK7 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_381,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK7),k6_mcart_1(X0,X1,X2,sK7)),k7_mcart_1(X0,X1,X2,sK7)) = sK7
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_1372,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_381])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_69,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_72,plain,
    ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_582,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1267,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_1268,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_1269,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_1270,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_1271,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_1272,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_1892,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1372,c_36,c_35,c_34,c_69,c_72,c_1268,c_1270,c_1272])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_362,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | sK7 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_363,plain,
    ( k7_mcart_1(X0,X1,X2,sK7) = k2_mcart_1(sK7)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_1336,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(sK7)
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_363])).

cnf(c_1636,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1336,c_36,c_35,c_34,c_69,c_72,c_1268,c_1270,c_1272])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_326,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | sK7 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_327,plain,
    ( k5_mcart_1(X0,X1,X2,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_1342,plain,
    ( k5_mcart_1(sK4,sK5,sK6,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_327])).

cnf(c_1675,plain,
    ( k5_mcart_1(sK4,sK5,sK6,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1342,c_36,c_35,c_34,c_69,c_72,c_1268,c_1270,c_1272])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_344,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | sK7 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_33])).

cnf(c_345,plain,
    ( k6_mcart_1(X0,X1,X2,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_1366,plain,
    ( k6_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_345])).

cnf(c_1886,plain,
    ( k6_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1366,c_36,c_35,c_34,c_69,c_72,c_1268,c_1270,c_1272])).

cnf(c_1894,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))),k2_mcart_1(sK7)) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_1892,c_1636,c_1675,c_1886])).

cnf(c_21,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_30,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1009,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_21,c_30])).

cnf(c_1896,plain,
    ( k2_mcart_1(sK7) != sK7 ),
    inference(superposition,[status(thm)],[c_1894,c_1009])).

cnf(c_32,negated_conjecture,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1639,plain,
    ( k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k2_mcart_1(sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_32,c_1636])).

cnf(c_1889,plain,
    ( k5_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | k2_mcart_1(sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_1639,c_1886])).

cnf(c_1891,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = sK7
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | k2_mcart_1(sK7) = sK7 ),
    inference(demodulation,[status(thm)],[c_1889,c_1675])).

cnf(c_1965,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = sK7
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1896,c_1891])).

cnf(c_31,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1898,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
    inference(superposition,[status(thm)],[c_1894,c_31])).

cnf(c_2187,plain,
    ( k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_1965,c_1898])).

cnf(c_25,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_964,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_970,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3068,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK3(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_964,c_970])).

cnf(c_1900,plain,
    ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 ),
    inference(demodulation,[status(thm)],[c_1898,c_1894])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK3(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_965,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK3(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2028,plain,
    ( k4_tarski(sK7,X0) != sK3(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k1_mcart_1(sK7),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1900,c_965])).

cnf(c_3762,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | k4_tarski(sK7,X1) != X0
    | r2_hidden(k1_mcart_1(sK7),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3068,c_2028])).

cnf(c_4158,plain,
    ( k1_enumset1(k4_tarski(sK7,X0),k4_tarski(sK7,X0),k4_tarski(sK7,X0)) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK7),k1_enumset1(k4_tarski(sK7,X0),k4_tarski(sK7,X0),k4_tarski(sK7,X0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3762])).

cnf(c_5137,plain,
    ( k1_enumset1(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7)))) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k1_mcart_1(sK7),k1_enumset1(k1_mcart_1(sK7),k1_mcart_1(sK7),k1_mcart_1(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2187,c_4158])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_975,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5199,plain,
    ( k1_enumset1(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7)))) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5137,c_975])).

cnf(c_5200,plain,
    ( k1_enumset1(k1_mcart_1(sK7),k1_mcart_1(sK7),k1_mcart_1(sK7)) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_2187,c_5199])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_enumset1(X2,X2,X0),X1) != k1_enumset1(X2,X2,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_968,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5250,plain,
    ( k1_enumset1(k1_mcart_1(sK7),k1_mcart_1(sK7),k1_mcart_1(sK7)) != k4_xboole_0(k1_xboole_0,X0)
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k1_mcart_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5200,c_968])).

cnf(c_5464,plain,
    ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k1_mcart_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5200,c_5250])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_982,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3077,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK3(k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_982])).

cnf(c_3079,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3077])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_983,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3289,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK3(k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_983])).

cnf(c_3291,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3289])).

cnf(c_5243,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k1_mcart_1(sK7),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5200,c_975])).

cnf(c_5466,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k1_mcart_1(sK7),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5464])).

cnf(c_5469,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5464,c_3079,c_3291,c_5243,c_5466])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK3(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_966,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK3(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2846,plain,
    ( k4_tarski(k1_mcart_1(sK7),X0) != sK3(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1898,c_966])).

cnf(c_3414,plain,
    ( sK3(X0) != sK7
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1900,c_2846])).

cnf(c_3755,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK7 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3068,c_3414])).

cnf(c_5477,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK7 != X0
    | r2_hidden(sK7,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5469,c_3755])).

cnf(c_6456,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | r2_hidden(sK7,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5477,c_970])).

cnf(c_6461,plain,
    ( k1_enumset1(sK7,sK7,sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_977,c_6456])).

cnf(c_6828,plain,
    ( k1_enumset1(sK7,sK7,sK7) != k4_xboole_0(k1_xboole_0,X0)
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6461,c_968])).

cnf(c_6830,plain,
    ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6828,c_6461])).

cnf(c_6846,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r2_hidden(sK7,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6830])).

cnf(c_6821,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6461,c_975])).

cnf(c_6051,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3077,c_3289])).

cnf(c_6079,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6051])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6846,c_6821,c_6079])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.60/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.01  
% 3.60/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/1.01  
% 3.60/1.01  ------  iProver source info
% 3.60/1.01  
% 3.60/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.60/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/1.01  git: non_committed_changes: false
% 3.60/1.01  git: last_make_outside_of_git: false
% 3.60/1.01  
% 3.60/1.01  ------ 
% 3.60/1.01  
% 3.60/1.01  ------ Input Options
% 3.60/1.01  
% 3.60/1.01  --out_options                           all
% 3.60/1.01  --tptp_safe_out                         true
% 3.60/1.01  --problem_path                          ""
% 3.60/1.01  --include_path                          ""
% 3.60/1.01  --clausifier                            res/vclausify_rel
% 3.60/1.01  --clausifier_options                    --mode clausify
% 3.60/1.01  --stdin                                 false
% 3.60/1.01  --stats_out                             all
% 3.60/1.01  
% 3.60/1.01  ------ General Options
% 3.60/1.01  
% 3.60/1.01  --fof                                   false
% 3.60/1.01  --time_out_real                         305.
% 3.60/1.01  --time_out_virtual                      -1.
% 3.60/1.01  --symbol_type_check                     false
% 3.60/1.01  --clausify_out                          false
% 3.60/1.01  --sig_cnt_out                           false
% 3.60/1.01  --trig_cnt_out                          false
% 3.60/1.01  --trig_cnt_out_tolerance                1.
% 3.60/1.01  --trig_cnt_out_sk_spl                   false
% 3.60/1.01  --abstr_cl_out                          false
% 3.60/1.01  
% 3.60/1.01  ------ Global Options
% 3.60/1.01  
% 3.60/1.01  --schedule                              default
% 3.60/1.01  --add_important_lit                     false
% 3.60/1.01  --prop_solver_per_cl                    1000
% 3.60/1.01  --min_unsat_core                        false
% 3.60/1.01  --soft_assumptions                      false
% 3.60/1.01  --soft_lemma_size                       3
% 3.60/1.01  --prop_impl_unit_size                   0
% 3.60/1.01  --prop_impl_unit                        []
% 3.60/1.01  --share_sel_clauses                     true
% 3.60/1.01  --reset_solvers                         false
% 3.60/1.01  --bc_imp_inh                            [conj_cone]
% 3.60/1.01  --conj_cone_tolerance                   3.
% 3.60/1.01  --extra_neg_conj                        none
% 3.60/1.01  --large_theory_mode                     true
% 3.60/1.01  --prolific_symb_bound                   200
% 3.60/1.01  --lt_threshold                          2000
% 3.60/1.01  --clause_weak_htbl                      true
% 3.60/1.01  --gc_record_bc_elim                     false
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing Options
% 3.60/1.01  
% 3.60/1.01  --preprocessing_flag                    true
% 3.60/1.01  --time_out_prep_mult                    0.1
% 3.60/1.01  --splitting_mode                        input
% 3.60/1.01  --splitting_grd                         true
% 3.60/1.01  --splitting_cvd                         false
% 3.60/1.01  --splitting_cvd_svl                     false
% 3.60/1.01  --splitting_nvd                         32
% 3.60/1.01  --sub_typing                            true
% 3.60/1.01  --prep_gs_sim                           true
% 3.60/1.01  --prep_unflatten                        true
% 3.60/1.01  --prep_res_sim                          true
% 3.60/1.01  --prep_upred                            true
% 3.60/1.01  --prep_sem_filter                       exhaustive
% 3.60/1.01  --prep_sem_filter_out                   false
% 3.60/1.01  --pred_elim                             true
% 3.60/1.01  --res_sim_input                         true
% 3.60/1.01  --eq_ax_congr_red                       true
% 3.60/1.01  --pure_diseq_elim                       true
% 3.60/1.01  --brand_transform                       false
% 3.60/1.01  --non_eq_to_eq                          false
% 3.60/1.01  --prep_def_merge                        true
% 3.60/1.01  --prep_def_merge_prop_impl              false
% 3.60/1.01  --prep_def_merge_mbd                    true
% 3.60/1.01  --prep_def_merge_tr_red                 false
% 3.60/1.01  --prep_def_merge_tr_cl                  false
% 3.60/1.01  --smt_preprocessing                     true
% 3.60/1.01  --smt_ac_axioms                         fast
% 3.60/1.01  --preprocessed_out                      false
% 3.60/1.01  --preprocessed_stats                    false
% 3.60/1.01  
% 3.60/1.01  ------ Abstraction refinement Options
% 3.60/1.01  
% 3.60/1.01  --abstr_ref                             []
% 3.60/1.01  --abstr_ref_prep                        false
% 3.60/1.01  --abstr_ref_until_sat                   false
% 3.60/1.01  --abstr_ref_sig_restrict                funpre
% 3.60/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.01  --abstr_ref_under                       []
% 3.60/1.01  
% 3.60/1.01  ------ SAT Options
% 3.60/1.01  
% 3.60/1.01  --sat_mode                              false
% 3.60/1.01  --sat_fm_restart_options                ""
% 3.60/1.01  --sat_gr_def                            false
% 3.60/1.01  --sat_epr_types                         true
% 3.60/1.01  --sat_non_cyclic_types                  false
% 3.60/1.01  --sat_finite_models                     false
% 3.60/1.01  --sat_fm_lemmas                         false
% 3.60/1.01  --sat_fm_prep                           false
% 3.60/1.01  --sat_fm_uc_incr                        true
% 3.60/1.01  --sat_out_model                         small
% 3.60/1.01  --sat_out_clauses                       false
% 3.60/1.01  
% 3.60/1.01  ------ QBF Options
% 3.60/1.01  
% 3.60/1.01  --qbf_mode                              false
% 3.60/1.01  --qbf_elim_univ                         false
% 3.60/1.01  --qbf_dom_inst                          none
% 3.60/1.01  --qbf_dom_pre_inst                      false
% 3.60/1.01  --qbf_sk_in                             false
% 3.60/1.01  --qbf_pred_elim                         true
% 3.60/1.01  --qbf_split                             512
% 3.60/1.01  
% 3.60/1.01  ------ BMC1 Options
% 3.60/1.01  
% 3.60/1.01  --bmc1_incremental                      false
% 3.60/1.01  --bmc1_axioms                           reachable_all
% 3.60/1.01  --bmc1_min_bound                        0
% 3.60/1.01  --bmc1_max_bound                        -1
% 3.60/1.01  --bmc1_max_bound_default                -1
% 3.60/1.01  --bmc1_symbol_reachability              true
% 3.60/1.01  --bmc1_property_lemmas                  false
% 3.60/1.01  --bmc1_k_induction                      false
% 3.60/1.01  --bmc1_non_equiv_states                 false
% 3.60/1.01  --bmc1_deadlock                         false
% 3.60/1.01  --bmc1_ucm                              false
% 3.60/1.01  --bmc1_add_unsat_core                   none
% 3.60/1.01  --bmc1_unsat_core_children              false
% 3.60/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.01  --bmc1_out_stat                         full
% 3.60/1.01  --bmc1_ground_init                      false
% 3.60/1.01  --bmc1_pre_inst_next_state              false
% 3.60/1.01  --bmc1_pre_inst_state                   false
% 3.60/1.01  --bmc1_pre_inst_reach_state             false
% 3.60/1.01  --bmc1_out_unsat_core                   false
% 3.60/1.01  --bmc1_aig_witness_out                  false
% 3.60/1.01  --bmc1_verbose                          false
% 3.60/1.01  --bmc1_dump_clauses_tptp                false
% 3.60/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.01  --bmc1_dump_file                        -
% 3.60/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.01  --bmc1_ucm_extend_mode                  1
% 3.60/1.01  --bmc1_ucm_init_mode                    2
% 3.60/1.01  --bmc1_ucm_cone_mode                    none
% 3.60/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.01  --bmc1_ucm_relax_model                  4
% 3.60/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.01  --bmc1_ucm_layered_model                none
% 3.60/1.01  --bmc1_ucm_max_lemma_size               10
% 3.60/1.01  
% 3.60/1.01  ------ AIG Options
% 3.60/1.01  
% 3.60/1.01  --aig_mode                              false
% 3.60/1.01  
% 3.60/1.01  ------ Instantiation Options
% 3.60/1.01  
% 3.60/1.01  --instantiation_flag                    true
% 3.60/1.01  --inst_sos_flag                         false
% 3.60/1.01  --inst_sos_phase                        true
% 3.60/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.01  --inst_lit_sel_side                     num_symb
% 3.60/1.01  --inst_solver_per_active                1400
% 3.60/1.01  --inst_solver_calls_frac                1.
% 3.60/1.01  --inst_passive_queue_type               priority_queues
% 3.60/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.01  --inst_passive_queues_freq              [25;2]
% 3.60/1.01  --inst_dismatching                      true
% 3.60/1.01  --inst_eager_unprocessed_to_passive     true
% 3.60/1.01  --inst_prop_sim_given                   true
% 3.60/1.01  --inst_prop_sim_new                     false
% 3.60/1.01  --inst_subs_new                         false
% 3.60/1.01  --inst_eq_res_simp                      false
% 3.60/1.01  --inst_subs_given                       false
% 3.60/1.01  --inst_orphan_elimination               true
% 3.60/1.01  --inst_learning_loop_flag               true
% 3.60/1.01  --inst_learning_start                   3000
% 3.60/1.01  --inst_learning_factor                  2
% 3.60/1.01  --inst_start_prop_sim_after_learn       3
% 3.60/1.01  --inst_sel_renew                        solver
% 3.60/1.01  --inst_lit_activity_flag                true
% 3.60/1.01  --inst_restr_to_given                   false
% 3.60/1.01  --inst_activity_threshold               500
% 3.60/1.01  --inst_out_proof                        true
% 3.60/1.01  
% 3.60/1.01  ------ Resolution Options
% 3.60/1.01  
% 3.60/1.01  --resolution_flag                       true
% 3.60/1.01  --res_lit_sel                           adaptive
% 3.60/1.01  --res_lit_sel_side                      none
% 3.60/1.01  --res_ordering                          kbo
% 3.60/1.01  --res_to_prop_solver                    active
% 3.60/1.01  --res_prop_simpl_new                    false
% 3.60/1.01  --res_prop_simpl_given                  true
% 3.60/1.01  --res_passive_queue_type                priority_queues
% 3.60/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.01  --res_passive_queues_freq               [15;5]
% 3.60/1.01  --res_forward_subs                      full
% 3.60/1.01  --res_backward_subs                     full
% 3.60/1.01  --res_forward_subs_resolution           true
% 3.60/1.01  --res_backward_subs_resolution          true
% 3.60/1.01  --res_orphan_elimination                true
% 3.60/1.01  --res_time_limit                        2.
% 3.60/1.01  --res_out_proof                         true
% 3.60/1.01  
% 3.60/1.01  ------ Superposition Options
% 3.60/1.01  
% 3.60/1.01  --superposition_flag                    true
% 3.60/1.01  --sup_passive_queue_type                priority_queues
% 3.60/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.01  --demod_completeness_check              fast
% 3.60/1.01  --demod_use_ground                      true
% 3.60/1.01  --sup_to_prop_solver                    passive
% 3.60/1.01  --sup_prop_simpl_new                    true
% 3.60/1.01  --sup_prop_simpl_given                  true
% 3.60/1.01  --sup_fun_splitting                     false
% 3.60/1.01  --sup_smt_interval                      50000
% 3.60/1.01  
% 3.60/1.01  ------ Superposition Simplification Setup
% 3.60/1.01  
% 3.60/1.01  --sup_indices_passive                   []
% 3.60/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.01  --sup_full_bw                           [BwDemod]
% 3.60/1.01  --sup_immed_triv                        [TrivRules]
% 3.60/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.01  --sup_immed_bw_main                     []
% 3.60/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.01  
% 3.60/1.01  ------ Combination Options
% 3.60/1.01  
% 3.60/1.01  --comb_res_mult                         3
% 3.60/1.01  --comb_sup_mult                         2
% 3.60/1.01  --comb_inst_mult                        10
% 3.60/1.01  
% 3.60/1.01  ------ Debug Options
% 3.60/1.01  
% 3.60/1.01  --dbg_backtrace                         false
% 3.60/1.01  --dbg_dump_prop_clauses                 false
% 3.60/1.01  --dbg_dump_prop_clauses_file            -
% 3.60/1.01  --dbg_out_stat                          false
% 3.60/1.01  ------ Parsing...
% 3.60/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/1.01  ------ Proving...
% 3.60/1.01  ------ Problem Properties 
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  clauses                                 36
% 3.60/1.01  conjectures                             4
% 3.60/1.01  EPR                                     3
% 3.60/1.01  Horn                                    22
% 3.60/1.01  unary                                   11
% 3.60/1.01  binary                                  6
% 3.60/1.01  lits                                    92
% 3.60/1.01  lits eq                                 59
% 3.60/1.01  fd_pure                                 0
% 3.60/1.01  fd_pseudo                               0
% 3.60/1.01  fd_cond                                 7
% 3.60/1.01  fd_pseudo_cond                          9
% 3.60/1.01  AC symbols                              0
% 3.60/1.01  
% 3.60/1.01  ------ Schedule dynamic 5 is on 
% 3.60/1.01  
% 3.60/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  ------ 
% 3.60/1.01  Current options:
% 3.60/1.01  ------ 
% 3.60/1.01  
% 3.60/1.01  ------ Input Options
% 3.60/1.01  
% 3.60/1.01  --out_options                           all
% 3.60/1.01  --tptp_safe_out                         true
% 3.60/1.01  --problem_path                          ""
% 3.60/1.01  --include_path                          ""
% 3.60/1.01  --clausifier                            res/vclausify_rel
% 3.60/1.01  --clausifier_options                    --mode clausify
% 3.60/1.01  --stdin                                 false
% 3.60/1.01  --stats_out                             all
% 3.60/1.01  
% 3.60/1.01  ------ General Options
% 3.60/1.01  
% 3.60/1.01  --fof                                   false
% 3.60/1.01  --time_out_real                         305.
% 3.60/1.01  --time_out_virtual                      -1.
% 3.60/1.01  --symbol_type_check                     false
% 3.60/1.01  --clausify_out                          false
% 3.60/1.01  --sig_cnt_out                           false
% 3.60/1.01  --trig_cnt_out                          false
% 3.60/1.01  --trig_cnt_out_tolerance                1.
% 3.60/1.01  --trig_cnt_out_sk_spl                   false
% 3.60/1.01  --abstr_cl_out                          false
% 3.60/1.01  
% 3.60/1.01  ------ Global Options
% 3.60/1.01  
% 3.60/1.01  --schedule                              default
% 3.60/1.01  --add_important_lit                     false
% 3.60/1.01  --prop_solver_per_cl                    1000
% 3.60/1.01  --min_unsat_core                        false
% 3.60/1.01  --soft_assumptions                      false
% 3.60/1.01  --soft_lemma_size                       3
% 3.60/1.01  --prop_impl_unit_size                   0
% 3.60/1.01  --prop_impl_unit                        []
% 3.60/1.01  --share_sel_clauses                     true
% 3.60/1.01  --reset_solvers                         false
% 3.60/1.01  --bc_imp_inh                            [conj_cone]
% 3.60/1.01  --conj_cone_tolerance                   3.
% 3.60/1.01  --extra_neg_conj                        none
% 3.60/1.01  --large_theory_mode                     true
% 3.60/1.01  --prolific_symb_bound                   200
% 3.60/1.01  --lt_threshold                          2000
% 3.60/1.01  --clause_weak_htbl                      true
% 3.60/1.01  --gc_record_bc_elim                     false
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing Options
% 3.60/1.01  
% 3.60/1.01  --preprocessing_flag                    true
% 3.60/1.01  --time_out_prep_mult                    0.1
% 3.60/1.01  --splitting_mode                        input
% 3.60/1.01  --splitting_grd                         true
% 3.60/1.01  --splitting_cvd                         false
% 3.60/1.01  --splitting_cvd_svl                     false
% 3.60/1.01  --splitting_nvd                         32
% 3.60/1.01  --sub_typing                            true
% 3.60/1.01  --prep_gs_sim                           true
% 3.60/1.01  --prep_unflatten                        true
% 3.60/1.01  --prep_res_sim                          true
% 3.60/1.01  --prep_upred                            true
% 3.60/1.01  --prep_sem_filter                       exhaustive
% 3.60/1.01  --prep_sem_filter_out                   false
% 3.60/1.01  --pred_elim                             true
% 3.60/1.01  --res_sim_input                         true
% 3.60/1.01  --eq_ax_congr_red                       true
% 3.60/1.01  --pure_diseq_elim                       true
% 3.60/1.01  --brand_transform                       false
% 3.60/1.01  --non_eq_to_eq                          false
% 3.60/1.01  --prep_def_merge                        true
% 3.60/1.01  --prep_def_merge_prop_impl              false
% 3.60/1.01  --prep_def_merge_mbd                    true
% 3.60/1.01  --prep_def_merge_tr_red                 false
% 3.60/1.01  --prep_def_merge_tr_cl                  false
% 3.60/1.01  --smt_preprocessing                     true
% 3.60/1.01  --smt_ac_axioms                         fast
% 3.60/1.01  --preprocessed_out                      false
% 3.60/1.01  --preprocessed_stats                    false
% 3.60/1.01  
% 3.60/1.01  ------ Abstraction refinement Options
% 3.60/1.01  
% 3.60/1.01  --abstr_ref                             []
% 3.60/1.01  --abstr_ref_prep                        false
% 3.60/1.01  --abstr_ref_until_sat                   false
% 3.60/1.01  --abstr_ref_sig_restrict                funpre
% 3.60/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.01  --abstr_ref_under                       []
% 3.60/1.01  
% 3.60/1.01  ------ SAT Options
% 3.60/1.01  
% 3.60/1.01  --sat_mode                              false
% 3.60/1.01  --sat_fm_restart_options                ""
% 3.60/1.01  --sat_gr_def                            false
% 3.60/1.01  --sat_epr_types                         true
% 3.60/1.01  --sat_non_cyclic_types                  false
% 3.60/1.01  --sat_finite_models                     false
% 3.60/1.01  --sat_fm_lemmas                         false
% 3.60/1.01  --sat_fm_prep                           false
% 3.60/1.01  --sat_fm_uc_incr                        true
% 3.60/1.01  --sat_out_model                         small
% 3.60/1.01  --sat_out_clauses                       false
% 3.60/1.01  
% 3.60/1.01  ------ QBF Options
% 3.60/1.01  
% 3.60/1.01  --qbf_mode                              false
% 3.60/1.01  --qbf_elim_univ                         false
% 3.60/1.01  --qbf_dom_inst                          none
% 3.60/1.01  --qbf_dom_pre_inst                      false
% 3.60/1.01  --qbf_sk_in                             false
% 3.60/1.01  --qbf_pred_elim                         true
% 3.60/1.01  --qbf_split                             512
% 3.60/1.01  
% 3.60/1.01  ------ BMC1 Options
% 3.60/1.01  
% 3.60/1.01  --bmc1_incremental                      false
% 3.60/1.01  --bmc1_axioms                           reachable_all
% 3.60/1.01  --bmc1_min_bound                        0
% 3.60/1.01  --bmc1_max_bound                        -1
% 3.60/1.01  --bmc1_max_bound_default                -1
% 3.60/1.01  --bmc1_symbol_reachability              true
% 3.60/1.01  --bmc1_property_lemmas                  false
% 3.60/1.01  --bmc1_k_induction                      false
% 3.60/1.01  --bmc1_non_equiv_states                 false
% 3.60/1.01  --bmc1_deadlock                         false
% 3.60/1.01  --bmc1_ucm                              false
% 3.60/1.01  --bmc1_add_unsat_core                   none
% 3.60/1.01  --bmc1_unsat_core_children              false
% 3.60/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.01  --bmc1_out_stat                         full
% 3.60/1.01  --bmc1_ground_init                      false
% 3.60/1.01  --bmc1_pre_inst_next_state              false
% 3.60/1.01  --bmc1_pre_inst_state                   false
% 3.60/1.01  --bmc1_pre_inst_reach_state             false
% 3.60/1.01  --bmc1_out_unsat_core                   false
% 3.60/1.01  --bmc1_aig_witness_out                  false
% 3.60/1.01  --bmc1_verbose                          false
% 3.60/1.01  --bmc1_dump_clauses_tptp                false
% 3.60/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.01  --bmc1_dump_file                        -
% 3.60/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.01  --bmc1_ucm_extend_mode                  1
% 3.60/1.01  --bmc1_ucm_init_mode                    2
% 3.60/1.01  --bmc1_ucm_cone_mode                    none
% 3.60/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.01  --bmc1_ucm_relax_model                  4
% 3.60/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.01  --bmc1_ucm_layered_model                none
% 3.60/1.01  --bmc1_ucm_max_lemma_size               10
% 3.60/1.01  
% 3.60/1.01  ------ AIG Options
% 3.60/1.01  
% 3.60/1.01  --aig_mode                              false
% 3.60/1.01  
% 3.60/1.01  ------ Instantiation Options
% 3.60/1.01  
% 3.60/1.01  --instantiation_flag                    true
% 3.60/1.01  --inst_sos_flag                         false
% 3.60/1.01  --inst_sos_phase                        true
% 3.60/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.01  --inst_lit_sel_side                     none
% 3.60/1.01  --inst_solver_per_active                1400
% 3.60/1.01  --inst_solver_calls_frac                1.
% 3.60/1.01  --inst_passive_queue_type               priority_queues
% 3.60/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.01  --inst_passive_queues_freq              [25;2]
% 3.60/1.01  --inst_dismatching                      true
% 3.60/1.01  --inst_eager_unprocessed_to_passive     true
% 3.60/1.01  --inst_prop_sim_given                   true
% 3.60/1.01  --inst_prop_sim_new                     false
% 3.60/1.01  --inst_subs_new                         false
% 3.60/1.01  --inst_eq_res_simp                      false
% 3.60/1.01  --inst_subs_given                       false
% 3.60/1.01  --inst_orphan_elimination               true
% 3.60/1.01  --inst_learning_loop_flag               true
% 3.60/1.01  --inst_learning_start                   3000
% 3.60/1.01  --inst_learning_factor                  2
% 3.60/1.01  --inst_start_prop_sim_after_learn       3
% 3.60/1.01  --inst_sel_renew                        solver
% 3.60/1.01  --inst_lit_activity_flag                true
% 3.60/1.01  --inst_restr_to_given                   false
% 3.60/1.01  --inst_activity_threshold               500
% 3.60/1.01  --inst_out_proof                        true
% 3.60/1.01  
% 3.60/1.01  ------ Resolution Options
% 3.60/1.01  
% 3.60/1.01  --resolution_flag                       false
% 3.60/1.01  --res_lit_sel                           adaptive
% 3.60/1.01  --res_lit_sel_side                      none
% 3.60/1.01  --res_ordering                          kbo
% 3.60/1.01  --res_to_prop_solver                    active
% 3.60/1.01  --res_prop_simpl_new                    false
% 3.60/1.01  --res_prop_simpl_given                  true
% 3.60/1.01  --res_passive_queue_type                priority_queues
% 3.60/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.01  --res_passive_queues_freq               [15;5]
% 3.60/1.01  --res_forward_subs                      full
% 3.60/1.01  --res_backward_subs                     full
% 3.60/1.01  --res_forward_subs_resolution           true
% 3.60/1.01  --res_backward_subs_resolution          true
% 3.60/1.01  --res_orphan_elimination                true
% 3.60/1.01  --res_time_limit                        2.
% 3.60/1.01  --res_out_proof                         true
% 3.60/1.01  
% 3.60/1.01  ------ Superposition Options
% 3.60/1.01  
% 3.60/1.01  --superposition_flag                    true
% 3.60/1.01  --sup_passive_queue_type                priority_queues
% 3.60/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.01  --demod_completeness_check              fast
% 3.60/1.01  --demod_use_ground                      true
% 3.60/1.01  --sup_to_prop_solver                    passive
% 3.60/1.01  --sup_prop_simpl_new                    true
% 3.60/1.01  --sup_prop_simpl_given                  true
% 3.60/1.01  --sup_fun_splitting                     false
% 3.60/1.01  --sup_smt_interval                      50000
% 3.60/1.01  
% 3.60/1.01  ------ Superposition Simplification Setup
% 3.60/1.01  
% 3.60/1.01  --sup_indices_passive                   []
% 3.60/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.01  --sup_full_bw                           [BwDemod]
% 3.60/1.01  --sup_immed_triv                        [TrivRules]
% 3.60/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.01  --sup_immed_bw_main                     []
% 3.60/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.01  
% 3.60/1.01  ------ Combination Options
% 3.60/1.01  
% 3.60/1.01  --comb_res_mult                         3
% 3.60/1.01  --comb_sup_mult                         2
% 3.60/1.01  --comb_inst_mult                        10
% 3.60/1.01  
% 3.60/1.01  ------ Debug Options
% 3.60/1.01  
% 3.60/1.01  --dbg_backtrace                         false
% 3.60/1.01  --dbg_dump_prop_clauses                 false
% 3.60/1.01  --dbg_dump_prop_clauses_file            -
% 3.60/1.01  --dbg_out_stat                          false
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  ------ Proving...
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  % SZS status Theorem for theBenchmark.p
% 3.60/1.01  
% 3.60/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/1.01  
% 3.60/1.01  fof(f2,axiom,(
% 3.60/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f16,plain,(
% 3.60/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.60/1.01    inference(ennf_transformation,[],[f2])).
% 3.60/1.01  
% 3.60/1.01  fof(f27,plain,(
% 3.60/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.60/1.01    inference(nnf_transformation,[],[f16])).
% 3.60/1.01  
% 3.60/1.01  fof(f28,plain,(
% 3.60/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.60/1.01    inference(flattening,[],[f27])).
% 3.60/1.01  
% 3.60/1.01  fof(f29,plain,(
% 3.60/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.60/1.01    inference(rectify,[],[f28])).
% 3.60/1.01  
% 3.60/1.01  fof(f30,plain,(
% 3.60/1.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f31,plain,(
% 3.60/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 3.60/1.01  
% 3.60/1.01  fof(f52,plain,(
% 3.60/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.60/1.01    inference(cnf_transformation,[],[f31])).
% 3.60/1.01  
% 3.60/1.01  fof(f102,plain,(
% 3.60/1.01    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 3.60/1.01    inference(equality_resolution,[],[f52])).
% 3.60/1.01  
% 3.60/1.01  fof(f103,plain,(
% 3.60/1.01    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 3.60/1.01    inference(equality_resolution,[],[f102])).
% 3.60/1.01  
% 3.60/1.01  fof(f11,axiom,(
% 3.60/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f19,plain,(
% 3.60/1.01    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.60/1.01    inference(ennf_transformation,[],[f11])).
% 3.60/1.01  
% 3.60/1.01  fof(f73,plain,(
% 3.60/1.01    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(cnf_transformation,[],[f19])).
% 3.60/1.01  
% 3.60/1.01  fof(f7,axiom,(
% 3.60/1.01    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f66,plain,(
% 3.60/1.01    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f7])).
% 3.60/1.01  
% 3.60/1.01  fof(f8,axiom,(
% 3.60/1.01    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f67,plain,(
% 3.60/1.01    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f8])).
% 3.60/1.01  
% 3.60/1.01  fof(f94,plain,(
% 3.60/1.01    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(definition_unfolding,[],[f73,f66,f67])).
% 3.60/1.01  
% 3.60/1.01  fof(f14,conjecture,(
% 3.60/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f15,negated_conjecture,(
% 3.60/1.01    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.60/1.01    inference(negated_conjecture,[],[f14])).
% 3.60/1.01  
% 3.60/1.01  fof(f21,plain,(
% 3.60/1.01    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.60/1.01    inference(ennf_transformation,[],[f15])).
% 3.60/1.01  
% 3.60/1.01  fof(f41,plain,(
% 3.60/1.01    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK7) = sK7 | k6_mcart_1(X0,X1,X2,sK7) = sK7 | k5_mcart_1(X0,X1,X2,sK7) = sK7) & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)))) )),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f40,plain,(
% 3.60/1.01    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK4,sK5,sK6,X3) = X3 | k6_mcart_1(sK4,sK5,sK6,X3) = X3 | k5_mcart_1(sK4,sK5,sK6,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK4,sK5,sK6))) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4)),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f42,plain,(
% 3.60/1.01    ((k7_mcart_1(sK4,sK5,sK6,sK7) = sK7 | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7 | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7) & m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6))) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4),
% 3.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f21,f41,f40])).
% 3.60/1.01  
% 3.60/1.01  fof(f82,plain,(
% 3.60/1.01    m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 3.60/1.01    inference(cnf_transformation,[],[f42])).
% 3.60/1.01  
% 3.60/1.01  fof(f98,plain,(
% 3.60/1.01    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 3.60/1.01    inference(definition_unfolding,[],[f82,f67])).
% 3.60/1.01  
% 3.60/1.01  fof(f79,plain,(
% 3.60/1.01    k1_xboole_0 != sK4),
% 3.60/1.01    inference(cnf_transformation,[],[f42])).
% 3.60/1.01  
% 3.60/1.01  fof(f80,plain,(
% 3.60/1.01    k1_xboole_0 != sK5),
% 3.60/1.01    inference(cnf_transformation,[],[f42])).
% 3.60/1.01  
% 3.60/1.01  fof(f81,plain,(
% 3.60/1.01    k1_xboole_0 != sK6),
% 3.60/1.01    inference(cnf_transformation,[],[f42])).
% 3.60/1.01  
% 3.60/1.01  fof(f3,axiom,(
% 3.60/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f32,plain,(
% 3.60/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.60/1.01    inference(nnf_transformation,[],[f3])).
% 3.60/1.01  
% 3.60/1.01  fof(f33,plain,(
% 3.60/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.60/1.01    inference(rectify,[],[f32])).
% 3.60/1.01  
% 3.60/1.01  fof(f34,plain,(
% 3.60/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f35,plain,(
% 3.60/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 3.60/1.01  
% 3.60/1.01  fof(f57,plain,(
% 3.60/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.60/1.01    inference(cnf_transformation,[],[f35])).
% 3.60/1.01  
% 3.60/1.01  fof(f4,axiom,(
% 3.60/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f61,plain,(
% 3.60/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f4])).
% 3.60/1.01  
% 3.60/1.01  fof(f5,axiom,(
% 3.60/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f62,plain,(
% 3.60/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f5])).
% 3.60/1.01  
% 3.60/1.01  fof(f84,plain,(
% 3.60/1.01    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 3.60/1.01    inference(definition_unfolding,[],[f61,f62])).
% 3.60/1.01  
% 3.60/1.01  fof(f88,plain,(
% 3.60/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 3.60/1.01    inference(definition_unfolding,[],[f57,f84])).
% 3.60/1.01  
% 3.60/1.01  fof(f111,plain,(
% 3.60/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 3.60/1.01    inference(equality_resolution,[],[f88])).
% 3.60/1.01  
% 3.60/1.01  fof(f58,plain,(
% 3.60/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.60/1.01    inference(cnf_transformation,[],[f35])).
% 3.60/1.01  
% 3.60/1.01  fof(f87,plain,(
% 3.60/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 3.60/1.01    inference(definition_unfolding,[],[f58,f84])).
% 3.60/1.01  
% 3.60/1.01  fof(f109,plain,(
% 3.60/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 3.60/1.01    inference(equality_resolution,[],[f87])).
% 3.60/1.01  
% 3.60/1.01  fof(f110,plain,(
% 3.60/1.01    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 3.60/1.01    inference(equality_resolution,[],[f109])).
% 3.60/1.01  
% 3.60/1.01  fof(f12,axiom,(
% 3.60/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f20,plain,(
% 3.60/1.01    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.60/1.01    inference(ennf_transformation,[],[f12])).
% 3.60/1.01  
% 3.60/1.01  fof(f76,plain,(
% 3.60/1.01    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(cnf_transformation,[],[f20])).
% 3.60/1.01  
% 3.60/1.01  fof(f95,plain,(
% 3.60/1.01    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(definition_unfolding,[],[f76,f67])).
% 3.60/1.01  
% 3.60/1.01  fof(f74,plain,(
% 3.60/1.01    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(cnf_transformation,[],[f20])).
% 3.60/1.01  
% 3.60/1.01  fof(f97,plain,(
% 3.60/1.01    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(definition_unfolding,[],[f74,f67])).
% 3.60/1.01  
% 3.60/1.01  fof(f75,plain,(
% 3.60/1.01    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(cnf_transformation,[],[f20])).
% 3.60/1.01  
% 3.60/1.01  fof(f96,plain,(
% 3.60/1.01    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(definition_unfolding,[],[f75,f67])).
% 3.60/1.01  
% 3.60/1.01  fof(f9,axiom,(
% 3.60/1.01    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f17,plain,(
% 3.60/1.01    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 3.60/1.01    inference(ennf_transformation,[],[f9])).
% 3.60/1.01  
% 3.60/1.01  fof(f69,plain,(
% 3.60/1.01    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 3.60/1.01    inference(cnf_transformation,[],[f17])).
% 3.60/1.01  
% 3.60/1.01  fof(f112,plain,(
% 3.60/1.01    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 3.60/1.01    inference(equality_resolution,[],[f69])).
% 3.60/1.01  
% 3.60/1.01  fof(f13,axiom,(
% 3.60/1.01    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f78,plain,(
% 3.60/1.01    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.60/1.01    inference(cnf_transformation,[],[f13])).
% 3.60/1.01  
% 3.60/1.01  fof(f83,plain,(
% 3.60/1.01    k7_mcart_1(sK4,sK5,sK6,sK7) = sK7 | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7 | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7),
% 3.60/1.01    inference(cnf_transformation,[],[f42])).
% 3.60/1.01  
% 3.60/1.01  fof(f77,plain,(
% 3.60/1.01    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.60/1.01    inference(cnf_transformation,[],[f13])).
% 3.60/1.01  
% 3.60/1.01  fof(f10,axiom,(
% 3.60/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f18,plain,(
% 3.60/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.60/1.01    inference(ennf_transformation,[],[f10])).
% 3.60/1.01  
% 3.60/1.01  fof(f38,plain,(
% 3.60/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f39,plain,(
% 3.60/1.01    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 3.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f38])).
% 3.60/1.01  
% 3.60/1.01  fof(f70,plain,(
% 3.60/1.01    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(cnf_transformation,[],[f39])).
% 3.60/1.01  
% 3.60/1.01  fof(f71,plain,(
% 3.60/1.01    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(cnf_transformation,[],[f39])).
% 3.60/1.01  
% 3.60/1.01  fof(f93,plain,(
% 3.60/1.01    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(definition_unfolding,[],[f71,f66])).
% 3.60/1.01  
% 3.60/1.01  fof(f50,plain,(
% 3.60/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.60/1.01    inference(cnf_transformation,[],[f31])).
% 3.60/1.01  
% 3.60/1.01  fof(f106,plain,(
% 3.60/1.01    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 3.60/1.01    inference(equality_resolution,[],[f50])).
% 3.60/1.01  
% 3.60/1.01  fof(f107,plain,(
% 3.60/1.01    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 3.60/1.01    inference(equality_resolution,[],[f106])).
% 3.60/1.01  
% 3.60/1.01  fof(f6,axiom,(
% 3.60/1.01    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f36,plain,(
% 3.60/1.01    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 3.60/1.01    inference(nnf_transformation,[],[f6])).
% 3.60/1.01  
% 3.60/1.01  fof(f37,plain,(
% 3.60/1.01    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 3.60/1.01    inference(flattening,[],[f36])).
% 3.60/1.01  
% 3.60/1.01  fof(f64,plain,(
% 3.60/1.01    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f37])).
% 3.60/1.01  
% 3.60/1.01  fof(f90,plain,(
% 3.60/1.01    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)) )),
% 3.60/1.01    inference(definition_unfolding,[],[f64,f62,f62])).
% 3.60/1.01  
% 3.60/1.01  fof(f1,axiom,(
% 3.60/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f22,plain,(
% 3.60/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.01    inference(nnf_transformation,[],[f1])).
% 3.60/1.01  
% 3.60/1.01  fof(f23,plain,(
% 3.60/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.01    inference(flattening,[],[f22])).
% 3.60/1.01  
% 3.60/1.01  fof(f24,plain,(
% 3.60/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.01    inference(rectify,[],[f23])).
% 3.60/1.01  
% 3.60/1.01  fof(f25,plain,(
% 3.60/1.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f26,plain,(
% 3.60/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.60/1.01  
% 3.60/1.01  fof(f43,plain,(
% 3.60/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.60/1.01    inference(cnf_transformation,[],[f26])).
% 3.60/1.01  
% 3.60/1.01  fof(f101,plain,(
% 3.60/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.60/1.01    inference(equality_resolution,[],[f43])).
% 3.60/1.01  
% 3.60/1.01  fof(f44,plain,(
% 3.60/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.60/1.01    inference(cnf_transformation,[],[f26])).
% 3.60/1.01  
% 3.60/1.01  fof(f100,plain,(
% 3.60/1.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.60/1.01    inference(equality_resolution,[],[f44])).
% 3.60/1.01  
% 3.60/1.01  fof(f72,plain,(
% 3.60/1.01    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(cnf_transformation,[],[f39])).
% 3.60/1.01  
% 3.60/1.01  fof(f92,plain,(
% 3.60/1.01    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.60/1.01    inference(definition_unfolding,[],[f72,f66])).
% 3.60/1.01  
% 3.60/1.01  cnf(c_10,plain,
% 3.60/1.01      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_977,plain,
% 3.60/1.01      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_26,plain,
% 3.60/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.60/1.01      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2
% 3.60/1.01      | k1_xboole_0 = X3 ),
% 3.60/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_33,negated_conjecture,
% 3.60/1.01      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_380,plain,
% 3.60/1.01      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.60/1.01      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 3.60/1.01      | sK7 != X3
% 3.60/1.01      | k1_xboole_0 = X0
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2 ),
% 3.60/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_381,plain,
% 3.60/1.01      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.60/1.01      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK7),k6_mcart_1(X0,X1,X2,sK7)),k7_mcart_1(X0,X1,X2,sK7)) = sK7
% 3.60/1.01      | k1_xboole_0 = X0
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2 ),
% 3.60/1.01      inference(unflattening,[status(thm)],[c_380]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1372,plain,
% 3.60/1.01      ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7
% 3.60/1.01      | sK6 = k1_xboole_0
% 3.60/1.01      | sK5 = k1_xboole_0
% 3.60/1.01      | sK4 = k1_xboole_0 ),
% 3.60/1.01      inference(equality_resolution,[status(thm)],[c_381]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_36,negated_conjecture,
% 3.60/1.01      ( k1_xboole_0 != sK4 ),
% 3.60/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_35,negated_conjecture,
% 3.60/1.01      ( k1_xboole_0 != sK5 ),
% 3.60/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_34,negated_conjecture,
% 3.60/1.01      ( k1_xboole_0 != sK6 ),
% 3.60/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_17,plain,
% 3.60/1.01      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 3.60/1.01      inference(cnf_transformation,[],[f111]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_69,plain,
% 3.60/1.01      ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.60/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_16,plain,
% 3.60/1.01      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f110]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_72,plain,
% 3.60/1.01      ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_582,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1267,plain,
% 3.60/1.01      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_582]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1268,plain,
% 3.60/1.01      ( sK6 != k1_xboole_0
% 3.60/1.01      | k1_xboole_0 = sK6
% 3.60/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_1267]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1269,plain,
% 3.60/1.01      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_582]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1270,plain,
% 3.60/1.01      ( sK5 != k1_xboole_0
% 3.60/1.01      | k1_xboole_0 = sK5
% 3.60/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_1269]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1271,plain,
% 3.60/1.01      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_582]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1272,plain,
% 3.60/1.01      ( sK4 != k1_xboole_0
% 3.60/1.01      | k1_xboole_0 = sK4
% 3.60/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_1271]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1892,plain,
% 3.60/1.01      ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7 ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_1372,c_36,c_35,c_34,c_69,c_72,c_1268,c_1270,c_1272]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_27,plain,
% 3.60/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.60/1.01      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2
% 3.60/1.01      | k1_xboole_0 = X3 ),
% 3.60/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_362,plain,
% 3.60/1.01      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.60/1.01      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.60/1.01      | sK7 != X3
% 3.60/1.01      | k1_xboole_0 = X0
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2 ),
% 3.60/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_363,plain,
% 3.60/1.01      ( k7_mcart_1(X0,X1,X2,sK7) = k2_mcart_1(sK7)
% 3.60/1.01      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.60/1.01      | k1_xboole_0 = X0
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2 ),
% 3.60/1.01      inference(unflattening,[status(thm)],[c_362]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1336,plain,
% 3.60/1.01      ( k7_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(sK7)
% 3.60/1.01      | sK6 = k1_xboole_0
% 3.60/1.01      | sK5 = k1_xboole_0
% 3.60/1.01      | sK4 = k1_xboole_0 ),
% 3.60/1.01      inference(equality_resolution,[status(thm)],[c_363]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1636,plain,
% 3.60/1.01      ( k7_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(sK7) ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_1336,c_36,c_35,c_34,c_69,c_72,c_1268,c_1270,c_1272]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_29,plain,
% 3.60/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.60/1.01      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2
% 3.60/1.01      | k1_xboole_0 = X3 ),
% 3.60/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_326,plain,
% 3.60/1.01      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.60/1.01      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.60/1.01      | sK7 != X3
% 3.60/1.01      | k1_xboole_0 = X0
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2 ),
% 3.60/1.01      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_327,plain,
% 3.60/1.01      ( k5_mcart_1(X0,X1,X2,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 3.60/1.01      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.60/1.01      | k1_xboole_0 = X0
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2 ),
% 3.60/1.01      inference(unflattening,[status(thm)],[c_326]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1342,plain,
% 3.60/1.01      ( k5_mcart_1(sK4,sK5,sK6,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 3.60/1.01      | sK6 = k1_xboole_0
% 3.60/1.01      | sK5 = k1_xboole_0
% 3.60/1.01      | sK4 = k1_xboole_0 ),
% 3.60/1.01      inference(equality_resolution,[status(thm)],[c_327]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1675,plain,
% 3.60/1.01      ( k5_mcart_1(sK4,sK5,sK6,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_1342,c_36,c_35,c_34,c_69,c_72,c_1268,c_1270,c_1272]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_28,plain,
% 3.60/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.60/1.01      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2
% 3.60/1.01      | k1_xboole_0 = X3 ),
% 3.60/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_344,plain,
% 3.60/1.01      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.60/1.01      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.60/1.01      | sK7 != X3
% 3.60/1.01      | k1_xboole_0 = X0
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2 ),
% 3.60/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_33]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_345,plain,
% 3.60/1.01      ( k6_mcart_1(X0,X1,X2,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 3.60/1.01      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.60/1.01      | k1_xboole_0 = X0
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | k1_xboole_0 = X2 ),
% 3.60/1.01      inference(unflattening,[status(thm)],[c_344]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1366,plain,
% 3.60/1.01      ( k6_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 3.60/1.01      | sK6 = k1_xboole_0
% 3.60/1.01      | sK5 = k1_xboole_0
% 3.60/1.01      | sK4 = k1_xboole_0 ),
% 3.60/1.01      inference(equality_resolution,[status(thm)],[c_345]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1886,plain,
% 3.60/1.01      ( k6_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_1366,c_36,c_35,c_34,c_69,c_72,c_1268,c_1270,c_1272]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1894,plain,
% 3.60/1.01      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))),k2_mcart_1(sK7)) = sK7 ),
% 3.60/1.01      inference(light_normalisation,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_1892,c_1636,c_1675,c_1886]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_21,plain,
% 3.60/1.01      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 3.60/1.01      inference(cnf_transformation,[],[f112]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_30,plain,
% 3.60/1.01      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.60/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1009,plain,
% 3.60/1.01      ( k4_tarski(X0,X1) != X1 ),
% 3.60/1.01      inference(light_normalisation,[status(thm)],[c_21,c_30]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1896,plain,
% 3.60/1.01      ( k2_mcart_1(sK7) != sK7 ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1894,c_1009]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_32,negated_conjecture,
% 3.60/1.01      ( k7_mcart_1(sK4,sK5,sK6,sK7) = sK7
% 3.60/1.01      | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
% 3.60/1.01      | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7 ),
% 3.60/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1639,plain,
% 3.60/1.01      ( k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
% 3.60/1.01      | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7
% 3.60/1.01      | k2_mcart_1(sK7) = sK7 ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_32,c_1636]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1889,plain,
% 3.60/1.01      ( k5_mcart_1(sK4,sK5,sK6,sK7) = sK7
% 3.60/1.01      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.60/1.01      | k2_mcart_1(sK7) = sK7 ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1639,c_1886]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1891,plain,
% 3.60/1.01      ( k1_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.60/1.01      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.60/1.01      | k2_mcart_1(sK7) = sK7 ),
% 3.60/1.01      inference(demodulation,[status(thm)],[c_1889,c_1675]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1965,plain,
% 3.60/1.01      ( k1_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.60/1.01      | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
% 3.60/1.01      inference(backward_subsumption_resolution,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_1896,c_1891]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_31,plain,
% 3.60/1.01      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.60/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1898,plain,
% 3.60/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1894,c_31]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2187,plain,
% 3.60/1.01      ( k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
% 3.60/1.01      | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1965,c_1898]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_25,plain,
% 3.60/1.01      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 3.60/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_964,plain,
% 3.60/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_970,plain,
% 3.60/1.01      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3068,plain,
% 3.60/1.01      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.60/1.01      | sK3(k1_enumset1(X0,X0,X0)) = X0 ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_964,c_970]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1900,plain,
% 3.60/1.01      ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 ),
% 3.60/1.01      inference(demodulation,[status(thm)],[c_1898,c_1894]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_24,plain,
% 3.60/1.01      ( ~ r2_hidden(X0,X1)
% 3.60/1.01      | k4_tarski(k4_tarski(X0,X2),X3) != sK3(X1)
% 3.60/1.01      | k1_xboole_0 = X1 ),
% 3.60/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_965,plain,
% 3.60/1.01      ( k4_tarski(k4_tarski(X0,X1),X2) != sK3(X3)
% 3.60/1.01      | k1_xboole_0 = X3
% 3.60/1.01      | r2_hidden(X0,X3) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2028,plain,
% 3.60/1.01      ( k4_tarski(sK7,X0) != sK3(X1)
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | r2_hidden(k1_mcart_1(sK7),X1) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1900,c_965]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3762,plain,
% 3.60/1.01      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.60/1.01      | k4_tarski(sK7,X1) != X0
% 3.60/1.01      | r2_hidden(k1_mcart_1(sK7),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_3068,c_2028]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_4158,plain,
% 3.60/1.01      ( k1_enumset1(k4_tarski(sK7,X0),k4_tarski(sK7,X0),k4_tarski(sK7,X0)) = k1_xboole_0
% 3.60/1.01      | r2_hidden(k1_mcart_1(sK7),k1_enumset1(k4_tarski(sK7,X0),k4_tarski(sK7,X0),k4_tarski(sK7,X0))) != iProver_top ),
% 3.60/1.01      inference(equality_resolution,[status(thm)],[c_3762]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5137,plain,
% 3.60/1.01      ( k1_enumset1(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7)))) = k1_xboole_0
% 3.60/1.01      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.60/1.01      | r2_hidden(k1_mcart_1(sK7),k1_enumset1(k1_mcart_1(sK7),k1_mcart_1(sK7),k1_mcart_1(sK7))) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_2187,c_4158]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_12,plain,
% 3.60/1.01      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f107]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_975,plain,
% 3.60/1.01      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5199,plain,
% 3.60/1.01      ( k1_enumset1(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7)))) = k1_xboole_0
% 3.60/1.01      | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
% 3.60/1.01      inference(forward_subsumption_resolution,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_5137,c_975]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5200,plain,
% 3.60/1.01      ( k1_enumset1(k1_mcart_1(sK7),k1_mcart_1(sK7),k1_mcart_1(sK7)) = k1_xboole_0
% 3.60/1.01      | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_2187,c_5199]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_19,plain,
% 3.60/1.01      ( ~ r2_hidden(X0,X1)
% 3.60/1.01      | k4_xboole_0(k1_enumset1(X2,X2,X0),X1) != k1_enumset1(X2,X2,X0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_968,plain,
% 3.60/1.01      ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)
% 3.60/1.01      | r2_hidden(X1,X2) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5250,plain,
% 3.60/1.01      ( k1_enumset1(k1_mcart_1(sK7),k1_mcart_1(sK7),k1_mcart_1(sK7)) != k4_xboole_0(k1_xboole_0,X0)
% 3.60/1.01      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.60/1.01      | r2_hidden(k1_mcart_1(sK7),X0) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_5200,c_968]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5464,plain,
% 3.60/1.01      ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
% 3.60/1.01      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.60/1.01      | r2_hidden(k1_mcart_1(sK7),X0) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_5200,c_5250]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5,plain,
% 3.60/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_982,plain,
% 3.60/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.60/1.01      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3077,plain,
% 3.60/1.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.60/1.01      | r2_hidden(sK3(k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_964,c_982]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3079,plain,
% 3.60/1.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 3.60/1.01      | r2_hidden(sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_3077]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_4,plain,
% 3.60/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_983,plain,
% 3.60/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.60/1.01      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3289,plain,
% 3.60/1.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.60/1.01      | r2_hidden(sK3(k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_964,c_983]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3291,plain,
% 3.60/1.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 3.60/1.01      | r2_hidden(sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) != iProver_top ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_3289]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5243,plain,
% 3.60/1.01      ( k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.60/1.01      | r2_hidden(k1_mcart_1(sK7),k1_xboole_0) = iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_5200,c_975]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5466,plain,
% 3.60/1.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.60/1.01      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.60/1.01      | r2_hidden(k1_mcart_1(sK7),k1_xboole_0) != iProver_top ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_5464]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5469,plain,
% 3.60/1.01      ( k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_5464,c_3079,c_3291,c_5243,c_5466]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_23,plain,
% 3.60/1.01      ( ~ r2_hidden(X0,X1)
% 3.60/1.01      | k4_tarski(k4_tarski(X2,X0),X3) != sK3(X1)
% 3.60/1.01      | k1_xboole_0 = X1 ),
% 3.60/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_966,plain,
% 3.60/1.01      ( k4_tarski(k4_tarski(X0,X1),X2) != sK3(X3)
% 3.60/1.01      | k1_xboole_0 = X3
% 3.60/1.01      | r2_hidden(X1,X3) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2846,plain,
% 3.60/1.01      ( k4_tarski(k1_mcart_1(sK7),X0) != sK3(X1)
% 3.60/1.01      | k1_xboole_0 = X1
% 3.60/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X1) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1898,c_966]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3414,plain,
% 3.60/1.01      ( sK3(X0) != sK7
% 3.60/1.01      | k1_xboole_0 = X0
% 3.60/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1900,c_2846]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3755,plain,
% 3.60/1.01      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.60/1.01      | sK7 != X0
% 3.60/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_3068,c_3414]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5477,plain,
% 3.60/1.01      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.60/1.01      | sK7 != X0
% 3.60/1.01      | r2_hidden(sK7,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.60/1.01      inference(demodulation,[status(thm)],[c_5469,c_3755]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_6456,plain,
% 3.60/1.01      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.60/1.01      | r2_hidden(sK7,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.60/1.01      inference(forward_subsumption_resolution,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_5477,c_970]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_6461,plain,
% 3.60/1.01      ( k1_enumset1(sK7,sK7,sK7) = k1_xboole_0 ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_977,c_6456]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_6828,plain,
% 3.60/1.01      ( k1_enumset1(sK7,sK7,sK7) != k4_xboole_0(k1_xboole_0,X0)
% 3.60/1.01      | r2_hidden(sK7,X0) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_6461,c_968]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_6830,plain,
% 3.60/1.01      ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
% 3.60/1.01      | r2_hidden(sK7,X0) != iProver_top ),
% 3.60/1.01      inference(light_normalisation,[status(thm)],[c_6828,c_6461]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_6846,plain,
% 3.60/1.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.60/1.01      | r2_hidden(sK7,k1_xboole_0) != iProver_top ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_6830]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_6821,plain,
% 3.60/1.01      ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_6461,c_975]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_6051,plain,
% 3.60/1.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_3077,c_3289]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_6079,plain,
% 3.60/1.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_6051]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(contradiction,plain,
% 3.60/1.01      ( $false ),
% 3.60/1.01      inference(minisat,[status(thm)],[c_6846,c_6821,c_6079]) ).
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/1.01  
% 3.60/1.01  ------                               Statistics
% 3.60/1.01  
% 3.60/1.01  ------ General
% 3.60/1.01  
% 3.60/1.01  abstr_ref_over_cycles:                  0
% 3.60/1.01  abstr_ref_under_cycles:                 0
% 3.60/1.01  gc_basic_clause_elim:                   0
% 3.60/1.01  forced_gc_time:                         0
% 3.60/1.01  parsing_time:                           0.01
% 3.60/1.01  unif_index_cands_time:                  0.
% 3.60/1.01  unif_index_add_time:                    0.
% 3.60/1.01  orderings_time:                         0.
% 3.60/1.01  out_proof_time:                         0.016
% 3.60/1.01  total_time:                             0.291
% 3.60/1.01  num_of_symbols:                         51
% 3.60/1.01  num_of_terms:                           8725
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing
% 3.60/1.01  
% 3.60/1.01  num_of_splits:                          0
% 3.60/1.01  num_of_split_atoms:                     0
% 3.60/1.01  num_of_reused_defs:                     0
% 3.60/1.01  num_eq_ax_congr_red:                    42
% 3.60/1.01  num_of_sem_filtered_clauses:            1
% 3.60/1.01  num_of_subtypes:                        0
% 3.60/1.01  monotx_restored_types:                  0
% 3.60/1.01  sat_num_of_epr_types:                   0
% 3.60/1.01  sat_num_of_non_cyclic_types:            0
% 3.60/1.01  sat_guarded_non_collapsed_types:        0
% 3.60/1.01  num_pure_diseq_elim:                    0
% 3.60/1.01  simp_replaced_by:                       0
% 3.60/1.01  res_preprocessed:                       168
% 3.60/1.01  prep_upred:                             0
% 3.60/1.01  prep_unflattend:                        4
% 3.60/1.01  smt_new_axioms:                         0
% 3.60/1.01  pred_elim_cands:                        1
% 3.60/1.01  pred_elim:                              1
% 3.60/1.01  pred_elim_cl:                           1
% 3.60/1.01  pred_elim_cycles:                       3
% 3.60/1.01  merged_defs:                            0
% 3.60/1.01  merged_defs_ncl:                        0
% 3.60/1.01  bin_hyper_res:                          0
% 3.60/1.01  prep_cycles:                            4
% 3.60/1.01  pred_elim_time:                         0.004
% 3.60/1.01  splitting_time:                         0.
% 3.60/1.01  sem_filter_time:                        0.
% 3.60/1.01  monotx_time:                            0.
% 3.60/1.01  subtype_inf_time:                       0.
% 3.60/1.01  
% 3.60/1.01  ------ Problem properties
% 3.60/1.01  
% 3.60/1.01  clauses:                                36
% 3.60/1.01  conjectures:                            4
% 3.60/1.01  epr:                                    3
% 3.60/1.01  horn:                                   22
% 3.60/1.01  ground:                                 4
% 3.60/1.01  unary:                                  11
% 3.60/1.01  binary:                                 6
% 3.60/1.01  lits:                                   92
% 3.60/1.01  lits_eq:                                59
% 3.60/1.01  fd_pure:                                0
% 3.60/1.01  fd_pseudo:                              0
% 3.60/1.01  fd_cond:                                7
% 3.60/1.01  fd_pseudo_cond:                         9
% 3.60/1.01  ac_symbols:                             0
% 3.60/1.01  
% 3.60/1.01  ------ Propositional Solver
% 3.60/1.01  
% 3.60/1.01  prop_solver_calls:                      27
% 3.60/1.01  prop_fast_solver_calls:                 1150
% 3.60/1.01  smt_solver_calls:                       0
% 3.60/1.01  smt_fast_solver_calls:                  0
% 3.60/1.01  prop_num_of_clauses:                    2892
% 3.60/1.01  prop_preprocess_simplified:             9456
% 3.60/1.01  prop_fo_subsumed:                       18
% 3.60/1.01  prop_solver_time:                       0.
% 3.60/1.01  smt_solver_time:                        0.
% 3.60/1.01  smt_fast_solver_time:                   0.
% 3.60/1.01  prop_fast_solver_time:                  0.
% 3.60/1.01  prop_unsat_core_time:                   0.
% 3.60/1.01  
% 3.60/1.01  ------ QBF
% 3.60/1.01  
% 3.60/1.01  qbf_q_res:                              0
% 3.60/1.01  qbf_num_tautologies:                    0
% 3.60/1.01  qbf_prep_cycles:                        0
% 3.60/1.01  
% 3.60/1.01  ------ BMC1
% 3.60/1.01  
% 3.60/1.01  bmc1_current_bound:                     -1
% 3.60/1.01  bmc1_last_solved_bound:                 -1
% 3.60/1.01  bmc1_unsat_core_size:                   -1
% 3.60/1.01  bmc1_unsat_core_parents_size:           -1
% 3.60/1.01  bmc1_merge_next_fun:                    0
% 3.60/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.60/1.01  
% 3.60/1.01  ------ Instantiation
% 3.60/1.01  
% 3.60/1.01  inst_num_of_clauses:                    969
% 3.60/1.01  inst_num_in_passive:                    409
% 3.60/1.01  inst_num_in_active:                     412
% 3.60/1.01  inst_num_in_unprocessed:                148
% 3.60/1.01  inst_num_of_loops:                      430
% 3.60/1.01  inst_num_of_learning_restarts:          0
% 3.60/1.01  inst_num_moves_active_passive:          17
% 3.60/1.01  inst_lit_activity:                      0
% 3.60/1.01  inst_lit_activity_moves:                0
% 3.60/1.01  inst_num_tautologies:                   0
% 3.60/1.01  inst_num_prop_implied:                  0
% 3.60/1.01  inst_num_existing_simplified:           0
% 3.60/1.01  inst_num_eq_res_simplified:             0
% 3.60/1.01  inst_num_child_elim:                    0
% 3.60/1.01  inst_num_of_dismatching_blockings:      141
% 3.60/1.01  inst_num_of_non_proper_insts:           999
% 3.60/1.01  inst_num_of_duplicates:                 0
% 3.60/1.01  inst_inst_num_from_inst_to_res:         0
% 3.60/1.01  inst_dismatching_checking_time:         0.
% 3.60/1.01  
% 3.60/1.01  ------ Resolution
% 3.60/1.01  
% 3.60/1.01  res_num_of_clauses:                     0
% 3.60/1.01  res_num_in_passive:                     0
% 3.60/1.01  res_num_in_active:                      0
% 3.60/1.01  res_num_of_loops:                       172
% 3.60/1.01  res_forward_subset_subsumed:            33
% 3.60/1.01  res_backward_subset_subsumed:           0
% 3.60/1.01  res_forward_subsumed:                   0
% 3.60/1.01  res_backward_subsumed:                  0
% 3.60/1.01  res_forward_subsumption_resolution:     0
% 3.60/1.01  res_backward_subsumption_resolution:    0
% 3.60/1.01  res_clause_to_clause_subsumption:       820
% 3.60/1.01  res_orphan_elimination:                 0
% 3.60/1.01  res_tautology_del:                      11
% 3.60/1.01  res_num_eq_res_simplified:              0
% 3.60/1.01  res_num_sel_changes:                    0
% 3.60/1.01  res_moves_from_active_to_pass:          0
% 3.60/1.01  
% 3.60/1.01  ------ Superposition
% 3.60/1.01  
% 3.60/1.01  sup_time_total:                         0.
% 3.60/1.01  sup_time_generating:                    0.
% 3.60/1.01  sup_time_sim_full:                      0.
% 3.60/1.01  sup_time_sim_immed:                     0.
% 3.60/1.01  
% 3.60/1.01  sup_num_of_clauses:                     128
% 3.60/1.01  sup_num_in_active:                      63
% 3.60/1.01  sup_num_in_passive:                     65
% 3.60/1.01  sup_num_of_loops:                       84
% 3.60/1.01  sup_fw_superposition:                   70
% 3.60/1.01  sup_bw_superposition:                   98
% 3.60/1.01  sup_immediate_simplified:               18
% 3.60/1.01  sup_given_eliminated:                   2
% 3.60/1.01  comparisons_done:                       0
% 3.60/1.01  comparisons_avoided:                    23
% 3.60/1.01  
% 3.60/1.01  ------ Simplifications
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  sim_fw_subset_subsumed:                 11
% 3.60/1.01  sim_bw_subset_subsumed:                 12
% 3.60/1.01  sim_fw_subsumed:                        6
% 3.60/1.01  sim_bw_subsumed:                        1
% 3.60/1.01  sim_fw_subsumption_res:                 3
% 3.60/1.01  sim_bw_subsumption_res:                 1
% 3.60/1.01  sim_tautology_del:                      4
% 3.60/1.01  sim_eq_tautology_del:                   10
% 3.60/1.01  sim_eq_res_simp:                        2
% 3.60/1.01  sim_fw_demodulated:                     1
% 3.60/1.01  sim_bw_demodulated:                     18
% 3.60/1.01  sim_light_normalised:                   6
% 3.60/1.01  sim_joinable_taut:                      0
% 3.60/1.01  sim_joinable_simp:                      0
% 3.60/1.01  sim_ac_normalised:                      0
% 3.60/1.01  sim_smt_subsumption:                    0
% 3.60/1.01  
%------------------------------------------------------------------------------
