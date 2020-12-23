%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:35 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  199 (8398 expanded)
%              Number of clauses        :  105 (1896 expanded)
%              Number of leaves         :   23 (2474 expanded)
%              Depth                    :   28
%              Number of atoms          :  668 (41570 expanded)
%              Number of equality atoms :  472 (32041 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f38])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f96])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f59])).

fof(f115,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f95])).

fof(f116,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f115])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f89])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f34])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f61,f84])).

fof(f118,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f98])).

fof(f9,axiom,(
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
    inference(nnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f59,f59])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( k7_mcart_1(X0,X1,X2,sK6) = sK6
          | k6_mcart_1(X0,X1,X2,sK6) = sK6
          | k5_mcart_1(X0,X1,X2,sK6) = sK6 )
        & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)) ) ) ),
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
          ( ( k7_mcart_1(sK3,sK4,sK5,X3) = X3
            | k6_mcart_1(sK3,sK4,sK5,X3) = X3
            | k5_mcart_1(sK3,sK4,sK5,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK3,sK4,sK5)) )
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3 ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 )
    & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f41,f40])).

fof(f82,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f109,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f82,f67])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f73,f66,f67])).

fof(f15,axiom,(
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

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f67])).

fof(f79,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f75,f67])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f67])).

fof(f71,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f104,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f71,f66])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f113,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f94])).

fof(f114,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f113])).

fof(f72,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f72,f66])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f84])).

fof(f83,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f78,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_24,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_658,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_667,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3186,plain,
    ( k1_enumset1(X0,X0,X1) = k1_xboole_0
    | sK2(k1_enumset1(X0,X0,X1)) = X0
    | sK2(k1_enumset1(X0,X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_658,c_667])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_79,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_674,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2293,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_674])).

cnf(c_7,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_665,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1611,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_665])).

cnf(c_2509,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2293,c_1611])).

cnf(c_2835,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_658,c_2509])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_661,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3322,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0
    | r2_hidden(X0,k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2835,c_661])).

cnf(c_14407,plain,
    ( sK2(k1_enumset1(X0,X0,X1)) = X0
    | sK2(k1_enumset1(X0,X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3186,c_79,c_3322])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_653,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_657,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6318,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_657])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_654,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1105,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_654])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1032,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1399,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1105,c_35,c_34,c_33,c_32,c_1032])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_655,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2524,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_655])).

cnf(c_1029,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3312,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2524,c_35,c_34,c_33,c_32,c_1029])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_656,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3924,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_656])).

cnf(c_1026,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_4592,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3924,c_35,c_34,c_33,c_32,c_1026])).

cnf(c_6319,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6318,c_1399,c_3312,c_4592])).

cnf(c_77,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_80,plain,
    ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_256,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_939,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_940,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_941,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_942,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_943,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_944,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_7175,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6319,c_35,c_34,c_33,c_77,c_80,c_940,c_942,c_944])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_659,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7185,plain,
    ( sK2(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7175,c_659])).

cnf(c_14417,plain,
    ( k1_enumset1(X0,X0,X1) = k1_xboole_0
    | sK2(k1_enumset1(X0,X0,X1)) = X0
    | sK6 != X1
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14407,c_7185])).

cnf(c_16833,plain,
    ( sK2(k1_enumset1(X0,X0,X1)) = X0
    | sK6 != X1
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14417,c_79,c_3322])).

cnf(c_16840,plain,
    ( sK2(k1_enumset1(X0,X0,sK6)) = X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_16833])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_4992,plain,
    ( r2_hidden(sK6,k1_enumset1(X0,X0,sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4993,plain,
    ( r2_hidden(sK6,k1_enumset1(X0,X0,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4992])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_660,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7184,plain,
    ( sK2(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7175,c_660])).

cnf(c_14418,plain,
    ( k1_enumset1(X0,X0,X1) = k1_xboole_0
    | sK2(k1_enumset1(X0,X0,X1)) = X0
    | sK6 != X1
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14407,c_7184])).

cnf(c_16845,plain,
    ( sK2(k1_enumset1(X0,X0,X1)) = X0
    | sK6 != X1
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14418,c_79,c_3322])).

cnf(c_669,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_666,plain,
    ( X0 = X1
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X0,X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3930,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_enumset1(X0,X0,X0)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2835,c_666])).

cnf(c_10839,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3930,c_1611])).

cnf(c_10850,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK2(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_658,c_10839])).

cnf(c_3454,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3322,c_79])).

cnf(c_10937,plain,
    ( sK2(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10850,c_3454])).

cnf(c_31,negated_conjecture,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4595,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_31,c_4592])).

cnf(c_4597,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(demodulation,[status(thm)],[c_4595,c_1399,c_3312])).

cnf(c_30,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_7183,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(superposition,[status(thm)],[c_7175,c_30])).

cnf(c_7450,plain,
    ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_4597,c_7183])).

cnf(c_7199,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(demodulation,[status(thm)],[c_7183,c_7175])).

cnf(c_20,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_29,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_702,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_20,c_29])).

cnf(c_7208,plain,
    ( k2_mcart_1(sK6) != sK6 ),
    inference(superposition,[status(thm)],[c_7199,c_702])).

cnf(c_7988,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7450,c_7208])).

cnf(c_7989,plain,
    ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(renaming,[status(thm)],[c_7988])).

cnf(c_7207,plain,
    ( k4_tarski(sK6,X0) != sK2(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k1_mcart_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7199,c_659])).

cnf(c_9907,plain,
    ( sK2(X0) != k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k1_xboole_0 = X0
    | r2_hidden(k1_mcart_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7989,c_7207])).

cnf(c_10939,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | k1_mcart_1(sK6) != X0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10937,c_9907])).

cnf(c_13651,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10939,c_10839,c_3454])).

cnf(c_13656,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_669,c_13651])).

cnf(c_16849,plain,
    ( sK2(k1_enumset1(X0,X0,X1)) = X0
    | sK6 != X1
    | r2_hidden(sK6,k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16845,c_13656])).

cnf(c_16854,plain,
    ( sK2(k1_enumset1(X0,X0,sK6)) = X0
    | r2_hidden(sK6,k1_enumset1(X0,X0,sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_16849])).

cnf(c_17470,plain,
    ( sK2(k1_enumset1(X0,X0,sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16840,c_4993,c_16854])).

cnf(c_17476,plain,
    ( k1_enumset1(X0,X0,sK6) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17470,c_7185])).

cnf(c_15059,plain,
    ( sK2(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13656,c_7184])).

cnf(c_17475,plain,
    ( k1_enumset1(X0,X0,sK6) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(sK6,k1_enumset1(X0,X0,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17470,c_15059])).

cnf(c_18211,plain,
    ( sK6 != X0
    | k1_enumset1(X0,X0,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17476,c_4993,c_17475])).

cnf(c_18212,plain,
    ( k1_enumset1(X0,X0,sK6) = k1_xboole_0
    | sK6 != X0 ),
    inference(renaming,[status(thm)],[c_18211])).

cnf(c_18216,plain,
    ( sK6 != X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18212,c_3454])).

cnf(c_18218,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_18216])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:12:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.52/1.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/1.54  
% 7.52/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.52/1.54  
% 7.52/1.54  ------  iProver source info
% 7.52/1.54  
% 7.52/1.54  git: date: 2020-06-30 10:37:57 +0100
% 7.52/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.52/1.54  git: non_committed_changes: false
% 7.52/1.54  git: last_make_outside_of_git: false
% 7.52/1.54  
% 7.52/1.54  ------ 
% 7.52/1.54  ------ Parsing...
% 7.52/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.52/1.54  
% 7.52/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.52/1.54  
% 7.52/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.52/1.54  
% 7.52/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.52/1.54  ------ Proving...
% 7.52/1.54  ------ Problem Properties 
% 7.52/1.54  
% 7.52/1.54  
% 7.52/1.54  clauses                                 36
% 7.52/1.54  conjectures                             5
% 7.52/1.54  EPR                                     3
% 7.52/1.54  Horn                                    24
% 7.52/1.54  unary                                   13
% 7.52/1.54  binary                                  6
% 7.52/1.54  lits                                    86
% 7.52/1.54  lits eq                                 49
% 7.52/1.54  fd_pure                                 0
% 7.52/1.54  fd_pseudo                               0
% 7.52/1.54  fd_cond                                 6
% 7.52/1.54  fd_pseudo_cond                          7
% 7.52/1.54  AC symbols                              0
% 7.52/1.54  
% 7.52/1.54  ------ Input Options Time Limit: Unbounded
% 7.52/1.54  
% 7.52/1.54  
% 7.52/1.54  ------ 
% 7.52/1.54  Current options:
% 7.52/1.54  ------ 
% 7.52/1.54  
% 7.52/1.54  
% 7.52/1.54  
% 7.52/1.54  
% 7.52/1.54  ------ Proving...
% 7.52/1.54  
% 7.52/1.54  
% 7.52/1.54  % SZS status Theorem for theBenchmark.p
% 7.52/1.54  
% 7.52/1.54   Resolution empty clause
% 7.52/1.54  
% 7.52/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 7.52/1.54  
% 7.52/1.54  fof(f13,axiom,(
% 7.52/1.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f20,plain,(
% 7.52/1.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 7.52/1.54    inference(ennf_transformation,[],[f13])).
% 7.52/1.54  
% 7.52/1.54  fof(f38,plain,(
% 7.52/1.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 7.52/1.54    introduced(choice_axiom,[])).
% 7.52/1.54  
% 7.52/1.54  fof(f39,plain,(
% 7.52/1.54    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 7.52/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f38])).
% 7.52/1.54  
% 7.52/1.54  fof(f70,plain,(
% 7.52/1.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(cnf_transformation,[],[f39])).
% 7.52/1.54  
% 7.52/1.54  fof(f5,axiom,(
% 7.52/1.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f29,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.52/1.54    inference(nnf_transformation,[],[f5])).
% 7.52/1.54  
% 7.52/1.54  fof(f30,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.52/1.54    inference(flattening,[],[f29])).
% 7.52/1.54  
% 7.52/1.54  fof(f31,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.52/1.54    inference(rectify,[],[f30])).
% 7.52/1.54  
% 7.52/1.54  fof(f32,plain,(
% 7.52/1.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.52/1.54    introduced(choice_axiom,[])).
% 7.52/1.54  
% 7.52/1.54  fof(f33,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.52/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 7.52/1.54  
% 7.52/1.54  fof(f52,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.52/1.54    inference(cnf_transformation,[],[f33])).
% 7.52/1.54  
% 7.52/1.54  fof(f7,axiom,(
% 7.52/1.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f59,plain,(
% 7.52/1.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.52/1.54    inference(cnf_transformation,[],[f7])).
% 7.52/1.54  
% 7.52/1.54  fof(f96,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 7.52/1.54    inference(definition_unfolding,[],[f52,f59])).
% 7.52/1.54  
% 7.52/1.54  fof(f117,plain,(
% 7.52/1.54    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 7.52/1.54    inference(equality_resolution,[],[f96])).
% 7.52/1.54  
% 7.52/1.54  fof(f53,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.52/1.54    inference(cnf_transformation,[],[f33])).
% 7.52/1.54  
% 7.52/1.54  fof(f95,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 7.52/1.54    inference(definition_unfolding,[],[f53,f59])).
% 7.52/1.54  
% 7.52/1.54  fof(f115,plain,(
% 7.52/1.54    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 7.52/1.54    inference(equality_resolution,[],[f95])).
% 7.52/1.54  
% 7.52/1.54  fof(f116,plain,(
% 7.52/1.54    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 7.52/1.54    inference(equality_resolution,[],[f115])).
% 7.52/1.54  
% 7.52/1.54  fof(f2,axiom,(
% 7.52/1.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f49,plain,(
% 7.52/1.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.52/1.54    inference(cnf_transformation,[],[f2])).
% 7.52/1.54  
% 7.52/1.54  fof(f1,axiom,(
% 7.52/1.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f24,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.52/1.54    inference(nnf_transformation,[],[f1])).
% 7.52/1.54  
% 7.52/1.54  fof(f25,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.52/1.54    inference(flattening,[],[f24])).
% 7.52/1.54  
% 7.52/1.54  fof(f26,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.52/1.54    inference(rectify,[],[f25])).
% 7.52/1.54  
% 7.52/1.54  fof(f27,plain,(
% 7.52/1.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.52/1.54    introduced(choice_axiom,[])).
% 7.52/1.54  
% 7.52/1.54  fof(f28,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.52/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 7.52/1.54  
% 7.52/1.54  fof(f44,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.52/1.54    inference(cnf_transformation,[],[f28])).
% 7.52/1.54  
% 7.52/1.54  fof(f3,axiom,(
% 7.52/1.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f50,plain,(
% 7.52/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.52/1.54    inference(cnf_transformation,[],[f3])).
% 7.52/1.54  
% 7.52/1.54  fof(f89,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 7.52/1.54    inference(definition_unfolding,[],[f44,f50])).
% 7.52/1.54  
% 7.52/1.54  fof(f111,plain,(
% 7.52/1.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.52/1.54    inference(equality_resolution,[],[f89])).
% 7.52/1.54  
% 7.52/1.54  fof(f4,axiom,(
% 7.52/1.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f51,plain,(
% 7.52/1.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 7.52/1.54    inference(cnf_transformation,[],[f4])).
% 7.52/1.54  
% 7.52/1.54  fof(f8,axiom,(
% 7.52/1.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f34,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.52/1.54    inference(nnf_transformation,[],[f8])).
% 7.52/1.54  
% 7.52/1.54  fof(f35,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.52/1.54    inference(flattening,[],[f34])).
% 7.52/1.54  
% 7.52/1.54  fof(f61,plain,(
% 7.52/1.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 7.52/1.54    inference(cnf_transformation,[],[f35])).
% 7.52/1.54  
% 7.52/1.54  fof(f6,axiom,(
% 7.52/1.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f58,plain,(
% 7.52/1.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.52/1.54    inference(cnf_transformation,[],[f6])).
% 7.52/1.54  
% 7.52/1.54  fof(f84,plain,(
% 7.52/1.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 7.52/1.54    inference(definition_unfolding,[],[f58,f59])).
% 7.52/1.54  
% 7.52/1.54  fof(f98,plain,(
% 7.52/1.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 7.52/1.54    inference(definition_unfolding,[],[f61,f84])).
% 7.52/1.54  
% 7.52/1.54  fof(f118,plain,(
% 7.52/1.54    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 7.52/1.54    inference(equality_resolution,[],[f98])).
% 7.52/1.54  
% 7.52/1.54  fof(f9,axiom,(
% 7.52/1.54    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f36,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 7.52/1.54    inference(nnf_transformation,[],[f9])).
% 7.52/1.54  
% 7.52/1.54  fof(f37,plain,(
% 7.52/1.54    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 7.52/1.54    inference(flattening,[],[f36])).
% 7.52/1.54  
% 7.52/1.54  fof(f63,plain,(
% 7.52/1.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 7.52/1.54    inference(cnf_transformation,[],[f37])).
% 7.52/1.54  
% 7.52/1.54  fof(f102,plain,(
% 7.52/1.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)) )),
% 7.52/1.54    inference(definition_unfolding,[],[f63,f59,f59])).
% 7.52/1.54  
% 7.52/1.54  fof(f17,conjecture,(
% 7.52/1.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f18,negated_conjecture,(
% 7.52/1.54    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.52/1.54    inference(negated_conjecture,[],[f17])).
% 7.52/1.54  
% 7.52/1.54  fof(f23,plain,(
% 7.52/1.54    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.52/1.54    inference(ennf_transformation,[],[f18])).
% 7.52/1.54  
% 7.52/1.54  fof(f41,plain,(
% 7.52/1.54    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK6) = sK6 | k6_mcart_1(X0,X1,X2,sK6) = sK6 | k5_mcart_1(X0,X1,X2,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)))) )),
% 7.52/1.54    introduced(choice_axiom,[])).
% 7.52/1.54  
% 7.52/1.54  fof(f40,plain,(
% 7.52/1.54    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK3,sK4,sK5,X3) = X3 | k6_mcart_1(sK3,sK4,sK5,X3) = X3 | k5_mcart_1(sK3,sK4,sK5,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3)),
% 7.52/1.54    introduced(choice_axiom,[])).
% 7.52/1.54  
% 7.52/1.54  fof(f42,plain,(
% 7.52/1.54    ((k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3),
% 7.52/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f41,f40])).
% 7.52/1.54  
% 7.52/1.54  fof(f82,plain,(
% 7.52/1.54    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 7.52/1.54    inference(cnf_transformation,[],[f42])).
% 7.52/1.54  
% 7.52/1.54  fof(f11,axiom,(
% 7.52/1.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f67,plain,(
% 7.52/1.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 7.52/1.54    inference(cnf_transformation,[],[f11])).
% 7.52/1.54  
% 7.52/1.54  fof(f109,plain,(
% 7.52/1.54    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 7.52/1.54    inference(definition_unfolding,[],[f82,f67])).
% 7.52/1.54  
% 7.52/1.54  fof(f14,axiom,(
% 7.52/1.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f21,plain,(
% 7.52/1.54    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.52/1.54    inference(ennf_transformation,[],[f14])).
% 7.52/1.54  
% 7.52/1.54  fof(f73,plain,(
% 7.52/1.54    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(cnf_transformation,[],[f21])).
% 7.52/1.54  
% 7.52/1.54  fof(f10,axiom,(
% 7.52/1.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f66,plain,(
% 7.52/1.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 7.52/1.54    inference(cnf_transformation,[],[f10])).
% 7.52/1.54  
% 7.52/1.54  fof(f105,plain,(
% 7.52/1.54    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(definition_unfolding,[],[f73,f66,f67])).
% 7.52/1.54  
% 7.52/1.54  fof(f15,axiom,(
% 7.52/1.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f22,plain,(
% 7.52/1.54    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.52/1.54    inference(ennf_transformation,[],[f15])).
% 7.52/1.54  
% 7.52/1.54  fof(f74,plain,(
% 7.52/1.54    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(cnf_transformation,[],[f22])).
% 7.52/1.54  
% 7.52/1.54  fof(f108,plain,(
% 7.52/1.54    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(definition_unfolding,[],[f74,f67])).
% 7.52/1.54  
% 7.52/1.54  fof(f79,plain,(
% 7.52/1.54    k1_xboole_0 != sK3),
% 7.52/1.54    inference(cnf_transformation,[],[f42])).
% 7.52/1.54  
% 7.52/1.54  fof(f80,plain,(
% 7.52/1.54    k1_xboole_0 != sK4),
% 7.52/1.54    inference(cnf_transformation,[],[f42])).
% 7.52/1.54  
% 7.52/1.54  fof(f81,plain,(
% 7.52/1.54    k1_xboole_0 != sK5),
% 7.52/1.54    inference(cnf_transformation,[],[f42])).
% 7.52/1.54  
% 7.52/1.54  fof(f75,plain,(
% 7.52/1.54    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(cnf_transformation,[],[f22])).
% 7.52/1.54  
% 7.52/1.54  fof(f107,plain,(
% 7.52/1.54    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(definition_unfolding,[],[f75,f67])).
% 7.52/1.54  
% 7.52/1.54  fof(f76,plain,(
% 7.52/1.54    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(cnf_transformation,[],[f22])).
% 7.52/1.54  
% 7.52/1.54  fof(f106,plain,(
% 7.52/1.54    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(definition_unfolding,[],[f76,f67])).
% 7.52/1.54  
% 7.52/1.54  fof(f71,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(cnf_transformation,[],[f39])).
% 7.52/1.54  
% 7.52/1.54  fof(f104,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(definition_unfolding,[],[f71,f66])).
% 7.52/1.54  
% 7.52/1.54  fof(f54,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.52/1.54    inference(cnf_transformation,[],[f33])).
% 7.52/1.54  
% 7.52/1.54  fof(f94,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 7.52/1.54    inference(definition_unfolding,[],[f54,f59])).
% 7.52/1.54  
% 7.52/1.54  fof(f113,plain,(
% 7.52/1.54    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 7.52/1.54    inference(equality_resolution,[],[f94])).
% 7.52/1.54  
% 7.52/1.54  fof(f114,plain,(
% 7.52/1.54    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 7.52/1.54    inference(equality_resolution,[],[f113])).
% 7.52/1.54  
% 7.52/1.54  fof(f72,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(cnf_transformation,[],[f39])).
% 7.52/1.54  
% 7.52/1.54  fof(f103,plain,(
% 7.52/1.54    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 7.52/1.54    inference(definition_unfolding,[],[f72,f66])).
% 7.52/1.54  
% 7.52/1.54  fof(f62,plain,(
% 7.52/1.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 7.52/1.54    inference(cnf_transformation,[],[f35])).
% 7.52/1.54  
% 7.52/1.54  fof(f97,plain,(
% 7.52/1.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 7.52/1.54    inference(definition_unfolding,[],[f62,f84])).
% 7.52/1.54  
% 7.52/1.54  fof(f83,plain,(
% 7.52/1.54    k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6),
% 7.52/1.54    inference(cnf_transformation,[],[f42])).
% 7.52/1.54  
% 7.52/1.54  fof(f16,axiom,(
% 7.52/1.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f77,plain,(
% 7.52/1.54    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 7.52/1.54    inference(cnf_transformation,[],[f16])).
% 7.52/1.54  
% 7.52/1.54  fof(f12,axiom,(
% 7.52/1.54    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 7.52/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.54  
% 7.52/1.54  fof(f19,plain,(
% 7.52/1.54    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 7.52/1.54    inference(ennf_transformation,[],[f12])).
% 7.52/1.54  
% 7.52/1.54  fof(f69,plain,(
% 7.52/1.54    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 7.52/1.54    inference(cnf_transformation,[],[f19])).
% 7.52/1.54  
% 7.52/1.54  fof(f119,plain,(
% 7.52/1.54    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 7.52/1.54    inference(equality_resolution,[],[f69])).
% 7.52/1.54  
% 7.52/1.54  fof(f78,plain,(
% 7.52/1.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 7.52/1.54    inference(cnf_transformation,[],[f16])).
% 7.52/1.54  
% 7.52/1.54  cnf(c_24,plain,
% 7.52/1.54      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 7.52/1.54      inference(cnf_transformation,[],[f70]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_658,plain,
% 7.52/1.54      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_13,plain,
% 7.52/1.54      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.52/1.54      inference(cnf_transformation,[],[f117]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_667,plain,
% 7.52/1.54      ( X0 = X1
% 7.52/1.54      | X0 = X2
% 7.52/1.54      | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_3186,plain,
% 7.52/1.54      ( k1_enumset1(X0,X0,X1) = k1_xboole_0
% 7.52/1.54      | sK2(k1_enumset1(X0,X0,X1)) = X0
% 7.52/1.54      | sK2(k1_enumset1(X0,X0,X1)) = X1 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_658,c_667]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_12,plain,
% 7.52/1.54      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 7.52/1.54      inference(cnf_transformation,[],[f116]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_79,plain,
% 7.52/1.54      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_6,plain,
% 7.52/1.54      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.52/1.54      inference(cnf_transformation,[],[f49]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_4,plain,
% 7.52/1.54      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 7.52/1.54      inference(cnf_transformation,[],[f111]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_674,plain,
% 7.52/1.54      ( r2_hidden(X0,X1) = iProver_top
% 7.52/1.54      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_2293,plain,
% 7.52/1.54      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
% 7.52/1.54      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_6,c_674]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7,plain,
% 7.52/1.54      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.52/1.54      inference(cnf_transformation,[],[f51]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_15,plain,
% 7.52/1.54      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) ),
% 7.52/1.54      inference(cnf_transformation,[],[f118]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_665,plain,
% 7.52/1.54      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) != iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_1611,plain,
% 7.52/1.54      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_7,c_665]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_2509,plain,
% 7.52/1.54      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
% 7.52/1.54      inference(global_propositional_subsumption,[status(thm)],[c_2293,c_1611]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_2835,plain,
% 7.52/1.54      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_658,c_2509]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_19,plain,
% 7.52/1.54      ( ~ r2_hidden(X0,X1)
% 7.52/1.54      | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_enumset1(X0,X0,X2) ),
% 7.52/1.54      inference(cnf_transformation,[],[f102]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_661,plain,
% 7.52/1.54      ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)
% 7.52/1.54      | r2_hidden(X0,X2) != iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_3322,plain,
% 7.52/1.54      ( k1_enumset1(X0,X0,X1) != k1_xboole_0
% 7.52/1.54      | r2_hidden(X0,k1_enumset1(X0,X0,X1)) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_2835,c_661]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_14407,plain,
% 7.52/1.54      ( sK2(k1_enumset1(X0,X0,X1)) = X0 | sK2(k1_enumset1(X0,X0,X1)) = X1 ),
% 7.52/1.54      inference(global_propositional_subsumption,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_3186,c_79,c_3322]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_32,negated_conjecture,
% 7.52/1.54      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 7.52/1.54      inference(cnf_transformation,[],[f109]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_653,plain,
% 7.52/1.54      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_25,plain,
% 7.52/1.54      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.52/1.54      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 7.52/1.54      | k1_xboole_0 = X1
% 7.52/1.54      | k1_xboole_0 = X2
% 7.52/1.54      | k1_xboole_0 = X3 ),
% 7.52/1.54      inference(cnf_transformation,[],[f105]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_657,plain,
% 7.52/1.54      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 7.52/1.54      | k1_xboole_0 = X0
% 7.52/1.54      | k1_xboole_0 = X1
% 7.52/1.54      | k1_xboole_0 = X2
% 7.52/1.54      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_6318,plain,
% 7.52/1.54      ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
% 7.52/1.54      | sK5 = k1_xboole_0
% 7.52/1.54      | sK4 = k1_xboole_0
% 7.52/1.54      | sK3 = k1_xboole_0 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_653,c_657]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_28,plain,
% 7.52/1.54      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.52/1.54      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 7.52/1.54      | k1_xboole_0 = X1
% 7.52/1.54      | k1_xboole_0 = X2
% 7.52/1.54      | k1_xboole_0 = X3 ),
% 7.52/1.54      inference(cnf_transformation,[],[f108]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_654,plain,
% 7.52/1.54      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 7.52/1.54      | k1_xboole_0 = X0
% 7.52/1.54      | k1_xboole_0 = X1
% 7.52/1.54      | k1_xboole_0 = X2
% 7.52/1.54      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_1105,plain,
% 7.52/1.54      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 7.52/1.54      | sK5 = k1_xboole_0
% 7.52/1.54      | sK4 = k1_xboole_0
% 7.52/1.54      | sK3 = k1_xboole_0 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_653,c_654]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_35,negated_conjecture,
% 7.52/1.54      ( k1_xboole_0 != sK3 ),
% 7.52/1.54      inference(cnf_transformation,[],[f79]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_34,negated_conjecture,
% 7.52/1.54      ( k1_xboole_0 != sK4 ),
% 7.52/1.54      inference(cnf_transformation,[],[f80]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_33,negated_conjecture,
% 7.52/1.54      ( k1_xboole_0 != sK5 ),
% 7.52/1.54      inference(cnf_transformation,[],[f81]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_1032,plain,
% 7.52/1.54      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
% 7.52/1.54      | k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 7.52/1.54      | k1_xboole_0 = sK5
% 7.52/1.54      | k1_xboole_0 = sK4
% 7.52/1.54      | k1_xboole_0 = sK3 ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_28]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_1399,plain,
% 7.52/1.54      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
% 7.52/1.54      inference(global_propositional_subsumption,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_1105,c_35,c_34,c_33,c_32,c_1032]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_27,plain,
% 7.52/1.54      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.52/1.54      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 7.52/1.54      | k1_xboole_0 = X1
% 7.52/1.54      | k1_xboole_0 = X2
% 7.52/1.54      | k1_xboole_0 = X3 ),
% 7.52/1.54      inference(cnf_transformation,[],[f107]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_655,plain,
% 7.52/1.54      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 7.52/1.54      | k1_xboole_0 = X0
% 7.52/1.54      | k1_xboole_0 = X1
% 7.52/1.54      | k1_xboole_0 = X2
% 7.52/1.54      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_2524,plain,
% 7.52/1.54      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 7.52/1.54      | sK5 = k1_xboole_0
% 7.52/1.54      | sK4 = k1_xboole_0
% 7.52/1.54      | sK3 = k1_xboole_0 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_653,c_655]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_1029,plain,
% 7.52/1.54      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
% 7.52/1.54      | k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 7.52/1.54      | k1_xboole_0 = sK5
% 7.52/1.54      | k1_xboole_0 = sK4
% 7.52/1.54      | k1_xboole_0 = sK3 ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_27]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_3312,plain,
% 7.52/1.54      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
% 7.52/1.54      inference(global_propositional_subsumption,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_2524,c_35,c_34,c_33,c_32,c_1029]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_26,plain,
% 7.52/1.54      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.52/1.54      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 7.52/1.54      | k1_xboole_0 = X1
% 7.52/1.54      | k1_xboole_0 = X2
% 7.52/1.54      | k1_xboole_0 = X3 ),
% 7.52/1.54      inference(cnf_transformation,[],[f106]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_656,plain,
% 7.52/1.54      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 7.52/1.54      | k1_xboole_0 = X0
% 7.52/1.54      | k1_xboole_0 = X1
% 7.52/1.54      | k1_xboole_0 = X2
% 7.52/1.54      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_3924,plain,
% 7.52/1.54      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
% 7.52/1.54      | sK5 = k1_xboole_0
% 7.52/1.54      | sK4 = k1_xboole_0
% 7.52/1.54      | sK3 = k1_xboole_0 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_653,c_656]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_1026,plain,
% 7.52/1.54      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
% 7.52/1.54      | k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
% 7.52/1.54      | k1_xboole_0 = sK5
% 7.52/1.54      | k1_xboole_0 = sK4
% 7.52/1.54      | k1_xboole_0 = sK3 ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_26]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_4592,plain,
% 7.52/1.54      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
% 7.52/1.54      inference(global_propositional_subsumption,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_3924,c_35,c_34,c_33,c_32,c_1026]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_6319,plain,
% 7.52/1.54      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6
% 7.52/1.54      | sK5 = k1_xboole_0
% 7.52/1.54      | sK4 = k1_xboole_0
% 7.52/1.54      | sK3 = k1_xboole_0 ),
% 7.52/1.54      inference(light_normalisation,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_6318,c_1399,c_3312,c_4592]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_77,plain,
% 7.52/1.54      ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.52/1.54      | k1_xboole_0 = k1_xboole_0 ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_13]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_80,plain,
% 7.52/1.54      ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_12]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_256,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_939,plain,
% 7.52/1.54      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_256]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_940,plain,
% 7.52/1.54      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_939]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_941,plain,
% 7.52/1.54      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_256]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_942,plain,
% 7.52/1.54      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_941]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_943,plain,
% 7.52/1.54      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_256]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_944,plain,
% 7.52/1.54      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_943]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7175,plain,
% 7.52/1.54      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
% 7.52/1.54      inference(global_propositional_subsumption,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_6319,c_35,c_34,c_33,c_77,c_80,c_940,c_942,c_944]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_23,plain,
% 7.52/1.54      ( ~ r2_hidden(X0,X1)
% 7.52/1.54      | k4_tarski(k4_tarski(X0,X2),X3) != sK2(X1)
% 7.52/1.54      | k1_xboole_0 = X1 ),
% 7.52/1.54      inference(cnf_transformation,[],[f104]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_659,plain,
% 7.52/1.54      ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
% 7.52/1.54      | k1_xboole_0 = X3
% 7.52/1.54      | r2_hidden(X0,X3) != iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7185,plain,
% 7.52/1.54      ( sK2(X0) != sK6
% 7.52/1.54      | k1_xboole_0 = X0
% 7.52/1.54      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_7175,c_659]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_14417,plain,
% 7.52/1.54      ( k1_enumset1(X0,X0,X1) = k1_xboole_0
% 7.52/1.54      | sK2(k1_enumset1(X0,X0,X1)) = X0
% 7.52/1.54      | sK6 != X1
% 7.52/1.54      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X1)) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_14407,c_7185]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_16833,plain,
% 7.52/1.54      ( sK2(k1_enumset1(X0,X0,X1)) = X0
% 7.52/1.54      | sK6 != X1
% 7.52/1.54      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X1)) != iProver_top ),
% 7.52/1.54      inference(global_propositional_subsumption,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_14417,c_79,c_3322]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_16840,plain,
% 7.52/1.54      ( sK2(k1_enumset1(X0,X0,sK6)) = X0
% 7.52/1.54      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,sK6)) != iProver_top ),
% 7.52/1.54      inference(equality_resolution,[status(thm)],[c_16833]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_11,plain,
% 7.52/1.54      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 7.52/1.54      inference(cnf_transformation,[],[f114]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_4992,plain,
% 7.52/1.54      ( r2_hidden(sK6,k1_enumset1(X0,X0,sK6)) ),
% 7.52/1.54      inference(instantiation,[status(thm)],[c_11]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_4993,plain,
% 7.52/1.54      ( r2_hidden(sK6,k1_enumset1(X0,X0,sK6)) = iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_4992]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_22,plain,
% 7.52/1.54      ( ~ r2_hidden(X0,X1)
% 7.52/1.54      | k4_tarski(k4_tarski(X2,X0),X3) != sK2(X1)
% 7.52/1.54      | k1_xboole_0 = X1 ),
% 7.52/1.54      inference(cnf_transformation,[],[f103]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_660,plain,
% 7.52/1.54      ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
% 7.52/1.54      | k1_xboole_0 = X3
% 7.52/1.54      | r2_hidden(X1,X3) != iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7184,plain,
% 7.52/1.54      ( sK2(X0) != sK6
% 7.52/1.54      | k1_xboole_0 = X0
% 7.52/1.54      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_7175,c_660]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_14418,plain,
% 7.52/1.54      ( k1_enumset1(X0,X0,X1) = k1_xboole_0
% 7.52/1.54      | sK2(k1_enumset1(X0,X0,X1)) = X0
% 7.52/1.54      | sK6 != X1
% 7.52/1.54      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X1)) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_14407,c_7184]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_16845,plain,
% 7.52/1.54      ( sK2(k1_enumset1(X0,X0,X1)) = X0
% 7.52/1.54      | sK6 != X1
% 7.52/1.54      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X1)) != iProver_top ),
% 7.52/1.54      inference(global_propositional_subsumption,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_14418,c_79,c_3322]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_669,plain,
% 7.52/1.54      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_14,plain,
% 7.52/1.54      ( ~ r2_hidden(X0,X1)
% 7.52/1.54      | r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
% 7.52/1.54      | X2 = X0 ),
% 7.52/1.54      inference(cnf_transformation,[],[f97]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_666,plain,
% 7.52/1.54      ( X0 = X1
% 7.52/1.54      | r2_hidden(X1,X2) != iProver_top
% 7.52/1.54      | r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X0,X0,X0))) = iProver_top ),
% 7.52/1.54      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_3930,plain,
% 7.52/1.54      ( X0 = X1
% 7.52/1.54      | r2_hidden(X1,k1_enumset1(X0,X0,X0)) != iProver_top
% 7.52/1.54      | r2_hidden(X1,k1_xboole_0) = iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_2835,c_666]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_10839,plain,
% 7.52/1.54      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 7.52/1.54      inference(forward_subsumption_resolution,[status(thm)],[c_3930,c_1611]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_10850,plain,
% 7.52/1.54      ( k1_enumset1(X0,X0,X0) = k1_xboole_0 | sK2(k1_enumset1(X0,X0,X0)) = X0 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_658,c_10839]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_3454,plain,
% 7.52/1.54      ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
% 7.52/1.54      inference(global_propositional_subsumption,[status(thm)],[c_3322,c_79]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_10937,plain,
% 7.52/1.54      ( sK2(k1_enumset1(X0,X0,X0)) = X0 ),
% 7.52/1.54      inference(forward_subsumption_resolution,[status(thm)],[c_10850,c_3454]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_31,negated_conjecture,
% 7.52/1.54      ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 7.52/1.54      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 7.52/1.54      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
% 7.52/1.54      inference(cnf_transformation,[],[f83]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_4595,plain,
% 7.52/1.54      ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 7.52/1.54      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 7.52/1.54      | k2_mcart_1(sK6) = sK6 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_31,c_4592]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_4597,plain,
% 7.52/1.54      ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
% 7.52/1.54      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 7.52/1.54      | k2_mcart_1(sK6) = sK6 ),
% 7.52/1.54      inference(demodulation,[status(thm)],[c_4595,c_1399,c_3312]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_30,plain,
% 7.52/1.54      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 7.52/1.54      inference(cnf_transformation,[],[f77]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7183,plain,
% 7.52/1.54      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_7175,c_30]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7450,plain,
% 7.52/1.54      ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 7.52/1.54      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 7.52/1.54      | k2_mcart_1(sK6) = sK6 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_4597,c_7183]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7199,plain,
% 7.52/1.54      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 7.52/1.54      inference(demodulation,[status(thm)],[c_7183,c_7175]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_20,plain,
% 7.52/1.54      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 7.52/1.54      inference(cnf_transformation,[],[f119]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_29,plain,
% 7.52/1.54      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 7.52/1.54      inference(cnf_transformation,[],[f78]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_702,plain,
% 7.52/1.54      ( k4_tarski(X0,X1) != X1 ),
% 7.52/1.54      inference(light_normalisation,[status(thm)],[c_20,c_29]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7208,plain,
% 7.52/1.54      ( k2_mcart_1(sK6) != sK6 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_7199,c_702]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7988,plain,
% 7.52/1.54      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 7.52/1.54      | k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 7.52/1.54      inference(global_propositional_subsumption,[status(thm)],[c_7450,c_7208]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7989,plain,
% 7.52/1.54      ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 7.52/1.54      | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 7.52/1.54      inference(renaming,[status(thm)],[c_7988]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_7207,plain,
% 7.52/1.54      ( k4_tarski(sK6,X0) != sK2(X1)
% 7.52/1.54      | k1_xboole_0 = X1
% 7.52/1.54      | r2_hidden(k1_mcart_1(sK6),X1) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_7199,c_659]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_9907,plain,
% 7.52/1.54      ( sK2(X0) != k1_mcart_1(sK6)
% 7.52/1.54      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 7.52/1.54      | k1_xboole_0 = X0
% 7.52/1.54      | r2_hidden(k1_mcart_1(sK6),X0) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_7989,c_7207]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_10939,plain,
% 7.52/1.54      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 7.52/1.54      | k1_mcart_1(sK6) != X0
% 7.52/1.54      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 7.52/1.54      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_10937,c_9907]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_13651,plain,
% 7.52/1.54      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 7.52/1.54      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 7.52/1.54      inference(forward_subsumption_resolution,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_10939,c_10839,c_3454]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_13656,plain,
% 7.52/1.54      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_669,c_13651]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_16849,plain,
% 7.52/1.54      ( sK2(k1_enumset1(X0,X0,X1)) = X0
% 7.52/1.54      | sK6 != X1
% 7.52/1.54      | r2_hidden(sK6,k1_enumset1(X0,X0,X1)) != iProver_top ),
% 7.52/1.54      inference(light_normalisation,[status(thm)],[c_16845,c_13656]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_16854,plain,
% 7.52/1.54      ( sK2(k1_enumset1(X0,X0,sK6)) = X0
% 7.52/1.54      | r2_hidden(sK6,k1_enumset1(X0,X0,sK6)) != iProver_top ),
% 7.52/1.54      inference(equality_resolution,[status(thm)],[c_16849]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_17470,plain,
% 7.52/1.54      ( sK2(k1_enumset1(X0,X0,sK6)) = X0 ),
% 7.52/1.54      inference(global_propositional_subsumption,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_16840,c_4993,c_16854]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_17476,plain,
% 7.52/1.54      ( k1_enumset1(X0,X0,sK6) = k1_xboole_0
% 7.52/1.54      | sK6 != X0
% 7.52/1.54      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,sK6)) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_17470,c_7185]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_15059,plain,
% 7.52/1.54      ( sK2(X0) != sK6 | k1_xboole_0 = X0 | r2_hidden(sK6,X0) != iProver_top ),
% 7.52/1.54      inference(demodulation,[status(thm)],[c_13656,c_7184]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_17475,plain,
% 7.52/1.54      ( k1_enumset1(X0,X0,sK6) = k1_xboole_0
% 7.52/1.54      | sK6 != X0
% 7.52/1.54      | r2_hidden(sK6,k1_enumset1(X0,X0,sK6)) != iProver_top ),
% 7.52/1.54      inference(superposition,[status(thm)],[c_17470,c_15059]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_18211,plain,
% 7.52/1.54      ( sK6 != X0 | k1_enumset1(X0,X0,sK6) = k1_xboole_0 ),
% 7.52/1.54      inference(global_propositional_subsumption,
% 7.52/1.54                [status(thm)],
% 7.52/1.54                [c_17476,c_4993,c_17475]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_18212,plain,
% 7.52/1.54      ( k1_enumset1(X0,X0,sK6) = k1_xboole_0 | sK6 != X0 ),
% 7.52/1.54      inference(renaming,[status(thm)],[c_18211]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_18216,plain,
% 7.52/1.54      ( sK6 != X0 ),
% 7.52/1.54      inference(forward_subsumption_resolution,[status(thm)],[c_18212,c_3454]) ).
% 7.52/1.54  
% 7.52/1.54  cnf(c_18218,plain,
% 7.52/1.54      ( $false ),
% 7.52/1.54      inference(equality_resolution,[status(thm)],[c_18216]) ).
% 7.52/1.54  
% 7.52/1.54  
% 7.52/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 7.52/1.54  
% 7.52/1.54  ------                               Statistics
% 7.52/1.54  
% 7.52/1.54  ------ Selected
% 7.52/1.54  
% 7.52/1.54  total_time:                             0.668
% 7.52/1.54  
%------------------------------------------------------------------------------
