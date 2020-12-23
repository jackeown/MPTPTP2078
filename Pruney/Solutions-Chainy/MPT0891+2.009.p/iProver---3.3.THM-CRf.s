%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:33 EST 2020

% Result     : Theorem 11.19s
% Output     : CNFRefutation 11.19s
% Verified   : 
% Statistics : Number of formulae       :  181 (2455 expanded)
%              Number of clauses        :   89 ( 567 expanded)
%              Number of leaves         :   23 ( 712 expanded)
%              Depth                    :   22
%              Number of atoms          :  645 (12526 expanded)
%              Number of equality atoms :  452 (9680 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
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

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
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

fof(f40,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f39])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f35])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f64,f87])).

fof(f117,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f95])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f87])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f62,f62])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f114,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f54])).

fof(f115,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f114])).

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

fof(f24,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 )
    & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f42,f41])).

fof(f85,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f106,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f85,f70])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f69,f70])).

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

fof(f23,plain,(
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

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f77,f70])).

fof(f82,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f78,f70])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f79,f70])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f116,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f75,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f75,f69])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f110,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f56])).

fof(f111,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f110])).

fof(f86,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f43])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f118,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f72])).

fof(f81,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f69])).

cnf(c_26,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_698,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_716,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2496,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_716])).

cnf(c_7,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_705,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2152,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_705])).

cnf(c_2778,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2496,c_2152])).

cnf(c_2785,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_698,c_2778])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_706,plain,
    ( X0 = X1
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X0,X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4362,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_enumset1(X0,X0,X0)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2785,c_706])).

cnf(c_10473,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4362,c_2152])).

cnf(c_10485,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK2(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_698,c_10473])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_701,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3585,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0
    | r2_hidden(X0,k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2785,c_701])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_708,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3770,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3585,c_708])).

cnf(c_11840,plain,
    ( sK2(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10485,c_3770])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_693,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_697,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6527,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_693,c_697])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_694,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1151,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_693,c_694])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1090,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1493,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1151,c_37,c_36,c_35,c_34,c_1090])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_695,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2512,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_693,c_695])).

cnf(c_1087,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3576,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2512,c_37,c_36,c_35,c_34,c_1087])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_696,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4356,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_693,c_696])).

cnf(c_1084,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_5000,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4356,c_37,c_36,c_35,c_34,c_1084])).

cnf(c_6528,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6527,c_1493,c_3576,c_5000])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_79,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_82,plain,
    ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_270,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_997,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_998,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_999,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_1000,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_1001,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_1002,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_7241,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6528,c_37,c_36,c_35,c_79,c_82,c_998,c_1000,c_1002])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_700,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7250,plain,
    ( sK2(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7241,c_700])).

cnf(c_11847,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11840,c_7250])).

cnf(c_12640,plain,
    ( sK6 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11847,c_3770])).

cnf(c_12644,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_12640])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_710,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_33,negated_conjecture,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5003,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_33,c_5000])).

cnf(c_5005,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(demodulation,[status(thm)],[c_5003,c_1493,c_3576])).

cnf(c_32,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_7249,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(superposition,[status(thm)],[c_7241,c_32])).

cnf(c_7953,plain,
    ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_5005,c_7249])).

cnf(c_7265,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(demodulation,[status(thm)],[c_7249,c_7241])).

cnf(c_22,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_31,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_746,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_22,c_31])).

cnf(c_7274,plain,
    ( k2_mcart_1(sK6) != sK6 ),
    inference(superposition,[status(thm)],[c_7265,c_746])).

cnf(c_8111,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7953,c_7274])).

cnf(c_8112,plain,
    ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(renaming,[status(thm)],[c_8111])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_699,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7273,plain,
    ( k4_tarski(sK6,X0) != sK2(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k1_mcart_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7265,c_699])).

cnf(c_9805,plain,
    ( sK2(X0) != k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k1_xboole_0 = X0
    | r2_hidden(k1_mcart_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8112,c_7273])).

cnf(c_11844,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | k1_mcart_1(sK6) != X0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11840,c_9805])).

cnf(c_12651,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11844,c_10473,c_3770])).

cnf(c_12656,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_710,c_12651])).

cnf(c_34343,plain,
    ( r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12644,c_12656])).

cnf(c_34345,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_34343,c_708])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 18:22:24 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 11.19/1.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.19/1.96  
% 11.19/1.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.19/1.96  
% 11.19/1.96  ------  iProver source info
% 11.19/1.96  
% 11.19/1.96  git: date: 2020-06-30 10:37:57 +0100
% 11.19/1.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.19/1.96  git: non_committed_changes: false
% 11.19/1.96  git: last_make_outside_of_git: false
% 11.19/1.96  
% 11.19/1.96  ------ 
% 11.19/1.96  ------ Parsing...
% 11.19/1.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.19/1.96  
% 11.19/1.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.19/1.96  
% 11.19/1.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.19/1.96  
% 11.19/1.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.19/1.96  ------ Proving...
% 11.19/1.96  ------ Problem Properties 
% 11.19/1.96  
% 11.19/1.96  
% 11.19/1.96  clauses                                 38
% 11.19/1.96  conjectures                             5
% 11.19/1.96  EPR                                     3
% 11.19/1.96  Horn                                    26
% 11.19/1.96  unary                                   14
% 11.19/1.96  binary                                  6
% 11.19/1.96  lits                                    92
% 11.19/1.96  lits eq                                 53
% 11.19/1.96  fd_pure                                 0
% 11.19/1.96  fd_pseudo                               0
% 11.19/1.96  fd_cond                                 6
% 11.19/1.96  fd_pseudo_cond                          8
% 11.19/1.96  AC symbols                              0
% 11.19/1.96  
% 11.19/1.96  ------ Input Options Time Limit: Unbounded
% 11.19/1.96  
% 11.19/1.96  
% 11.19/1.96  ------ 
% 11.19/1.96  Current options:
% 11.19/1.96  ------ 
% 11.19/1.96  
% 11.19/1.96  
% 11.19/1.96  
% 11.19/1.96  
% 11.19/1.96  ------ Proving...
% 11.19/1.96  
% 11.19/1.96  
% 11.19/1.96  % SZS status Theorem for theBenchmark.p
% 11.19/1.96  
% 11.19/1.96   Resolution empty clause
% 11.19/1.96  
% 11.19/1.96  % SZS output start CNFRefutation for theBenchmark.p
% 11.19/1.96  
% 11.19/1.96  fof(f13,axiom,(
% 11.19/1.96    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 11.19/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.96  
% 11.19/1.96  fof(f21,plain,(
% 11.19/1.96    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 11.19/1.96    inference(ennf_transformation,[],[f13])).
% 11.19/1.96  
% 11.19/1.96  fof(f39,plain,(
% 11.19/1.96    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 11.19/1.96    introduced(choice_axiom,[])).
% 11.19/1.96  
% 11.19/1.96  fof(f40,plain,(
% 11.19/1.96    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 11.19/1.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f39])).
% 11.19/1.96  
% 11.19/1.96  fof(f73,plain,(
% 11.19/1.96    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 11.19/1.96    inference(cnf_transformation,[],[f40])).
% 11.19/1.96  
% 11.19/1.96  fof(f2,axiom,(
% 11.19/1.96    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.19/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.96  
% 11.19/1.96  fof(f50,plain,(
% 11.19/1.96    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.19/1.96    inference(cnf_transformation,[],[f2])).
% 11.19/1.96  
% 11.19/1.96  fof(f1,axiom,(
% 11.19/1.96    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.19/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.96  
% 11.19/1.96  fof(f25,plain,(
% 11.19/1.96    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.19/1.96    inference(nnf_transformation,[],[f1])).
% 11.19/1.96  
% 11.19/1.96  fof(f26,plain,(
% 11.19/1.96    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.19/1.96    inference(flattening,[],[f25])).
% 11.19/1.96  
% 11.19/1.96  fof(f27,plain,(
% 11.19/1.96    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.19/1.96    inference(rectify,[],[f26])).
% 11.19/1.96  
% 11.19/1.96  fof(f28,plain,(
% 11.19/1.96    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.19/1.96    introduced(choice_axiom,[])).
% 11.19/1.96  
% 11.19/1.96  fof(f29,plain,(
% 11.19/1.96    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.19/1.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 11.19/1.96  
% 11.19/1.96  fof(f45,plain,(
% 11.19/1.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.19/1.97    inference(cnf_transformation,[],[f29])).
% 11.19/1.97  
% 11.19/1.97  fof(f3,axiom,(
% 11.19/1.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f51,plain,(
% 11.19/1.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.19/1.97    inference(cnf_transformation,[],[f3])).
% 11.19/1.97  
% 11.19/1.97  fof(f92,plain,(
% 11.19/1.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 11.19/1.97    inference(definition_unfolding,[],[f45,f51])).
% 11.19/1.97  
% 11.19/1.97  fof(f108,plain,(
% 11.19/1.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.19/1.97    inference(equality_resolution,[],[f92])).
% 11.19/1.97  
% 11.19/1.97  fof(f4,axiom,(
% 11.19/1.97    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f52,plain,(
% 11.19/1.97    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 11.19/1.97    inference(cnf_transformation,[],[f4])).
% 11.19/1.97  
% 11.19/1.97  fof(f8,axiom,(
% 11.19/1.97    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f35,plain,(
% 11.19/1.97    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 11.19/1.97    inference(nnf_transformation,[],[f8])).
% 11.19/1.97  
% 11.19/1.97  fof(f36,plain,(
% 11.19/1.97    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 11.19/1.97    inference(flattening,[],[f35])).
% 11.19/1.97  
% 11.19/1.97  fof(f64,plain,(
% 11.19/1.97    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 11.19/1.97    inference(cnf_transformation,[],[f36])).
% 11.19/1.97  
% 11.19/1.97  fof(f6,axiom,(
% 11.19/1.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f61,plain,(
% 11.19/1.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.19/1.97    inference(cnf_transformation,[],[f6])).
% 11.19/1.97  
% 11.19/1.97  fof(f7,axiom,(
% 11.19/1.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f62,plain,(
% 11.19/1.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.19/1.97    inference(cnf_transformation,[],[f7])).
% 11.19/1.97  
% 11.19/1.97  fof(f87,plain,(
% 11.19/1.97    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 11.19/1.97    inference(definition_unfolding,[],[f61,f62])).
% 11.19/1.97  
% 11.19/1.97  fof(f95,plain,(
% 11.19/1.97    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 11.19/1.97    inference(definition_unfolding,[],[f64,f87])).
% 11.19/1.97  
% 11.19/1.97  fof(f117,plain,(
% 11.19/1.97    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 11.19/1.97    inference(equality_resolution,[],[f95])).
% 11.19/1.97  
% 11.19/1.97  fof(f65,plain,(
% 11.19/1.97    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 11.19/1.97    inference(cnf_transformation,[],[f36])).
% 11.19/1.97  
% 11.19/1.97  fof(f94,plain,(
% 11.19/1.97    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 11.19/1.97    inference(definition_unfolding,[],[f65,f87])).
% 11.19/1.97  
% 11.19/1.97  fof(f9,axiom,(
% 11.19/1.97    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f37,plain,(
% 11.19/1.97    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 11.19/1.97    inference(nnf_transformation,[],[f9])).
% 11.19/1.97  
% 11.19/1.97  fof(f38,plain,(
% 11.19/1.97    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 11.19/1.97    inference(flattening,[],[f37])).
% 11.19/1.97  
% 11.19/1.97  fof(f66,plain,(
% 11.19/1.97    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 11.19/1.97    inference(cnf_transformation,[],[f38])).
% 11.19/1.97  
% 11.19/1.97  fof(f99,plain,(
% 11.19/1.97    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)) )),
% 11.19/1.97    inference(definition_unfolding,[],[f66,f62,f62])).
% 11.19/1.97  
% 11.19/1.97  fof(f5,axiom,(
% 11.19/1.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f19,plain,(
% 11.19/1.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.19/1.97    inference(ennf_transformation,[],[f5])).
% 11.19/1.97  
% 11.19/1.97  fof(f30,plain,(
% 11.19/1.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.19/1.97    inference(nnf_transformation,[],[f19])).
% 11.19/1.97  
% 11.19/1.97  fof(f31,plain,(
% 11.19/1.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.19/1.97    inference(flattening,[],[f30])).
% 11.19/1.97  
% 11.19/1.97  fof(f32,plain,(
% 11.19/1.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.19/1.97    inference(rectify,[],[f31])).
% 11.19/1.97  
% 11.19/1.97  fof(f33,plain,(
% 11.19/1.97    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 11.19/1.97    introduced(choice_axiom,[])).
% 11.19/1.97  
% 11.19/1.97  fof(f34,plain,(
% 11.19/1.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.19/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 11.19/1.97  
% 11.19/1.97  fof(f54,plain,(
% 11.19/1.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.19/1.97    inference(cnf_transformation,[],[f34])).
% 11.19/1.97  
% 11.19/1.97  fof(f114,plain,(
% 11.19/1.97    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 11.19/1.97    inference(equality_resolution,[],[f54])).
% 11.19/1.97  
% 11.19/1.97  fof(f115,plain,(
% 11.19/1.97    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 11.19/1.97    inference(equality_resolution,[],[f114])).
% 11.19/1.97  
% 11.19/1.97  fof(f17,conjecture,(
% 11.19/1.97    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f18,negated_conjecture,(
% 11.19/1.97    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 11.19/1.97    inference(negated_conjecture,[],[f17])).
% 11.19/1.97  
% 11.19/1.97  fof(f24,plain,(
% 11.19/1.97    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 11.19/1.97    inference(ennf_transformation,[],[f18])).
% 11.19/1.97  
% 11.19/1.97  fof(f42,plain,(
% 11.19/1.97    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK6) = sK6 | k6_mcart_1(X0,X1,X2,sK6) = sK6 | k5_mcart_1(X0,X1,X2,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)))) )),
% 11.19/1.97    introduced(choice_axiom,[])).
% 11.19/1.97  
% 11.19/1.97  fof(f41,plain,(
% 11.19/1.97    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK3,sK4,sK5,X3) = X3 | k6_mcart_1(sK3,sK4,sK5,X3) = X3 | k5_mcart_1(sK3,sK4,sK5,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3)),
% 11.19/1.97    introduced(choice_axiom,[])).
% 11.19/1.97  
% 11.19/1.97  fof(f43,plain,(
% 11.19/1.97    ((k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3),
% 11.19/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f42,f41])).
% 11.19/1.97  
% 11.19/1.97  fof(f85,plain,(
% 11.19/1.97    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 11.19/1.97    inference(cnf_transformation,[],[f43])).
% 11.19/1.97  
% 11.19/1.97  fof(f11,axiom,(
% 11.19/1.97    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f70,plain,(
% 11.19/1.97    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 11.19/1.97    inference(cnf_transformation,[],[f11])).
% 11.19/1.97  
% 11.19/1.97  fof(f106,plain,(
% 11.19/1.97    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 11.19/1.97    inference(definition_unfolding,[],[f85,f70])).
% 11.19/1.97  
% 11.19/1.97  fof(f14,axiom,(
% 11.19/1.97    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f22,plain,(
% 11.19/1.97    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 11.19/1.97    inference(ennf_transformation,[],[f14])).
% 11.19/1.97  
% 11.19/1.97  fof(f76,plain,(
% 11.19/1.97    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(cnf_transformation,[],[f22])).
% 11.19/1.97  
% 11.19/1.97  fof(f10,axiom,(
% 11.19/1.97    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f69,plain,(
% 11.19/1.97    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 11.19/1.97    inference(cnf_transformation,[],[f10])).
% 11.19/1.97  
% 11.19/1.97  fof(f102,plain,(
% 11.19/1.97    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(definition_unfolding,[],[f76,f69,f70])).
% 11.19/1.97  
% 11.19/1.97  fof(f15,axiom,(
% 11.19/1.97    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f23,plain,(
% 11.19/1.97    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 11.19/1.97    inference(ennf_transformation,[],[f15])).
% 11.19/1.97  
% 11.19/1.97  fof(f77,plain,(
% 11.19/1.97    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(cnf_transformation,[],[f23])).
% 11.19/1.97  
% 11.19/1.97  fof(f105,plain,(
% 11.19/1.97    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(definition_unfolding,[],[f77,f70])).
% 11.19/1.97  
% 11.19/1.97  fof(f82,plain,(
% 11.19/1.97    k1_xboole_0 != sK3),
% 11.19/1.97    inference(cnf_transformation,[],[f43])).
% 11.19/1.97  
% 11.19/1.97  fof(f83,plain,(
% 11.19/1.97    k1_xboole_0 != sK4),
% 11.19/1.97    inference(cnf_transformation,[],[f43])).
% 11.19/1.97  
% 11.19/1.97  fof(f84,plain,(
% 11.19/1.97    k1_xboole_0 != sK5),
% 11.19/1.97    inference(cnf_transformation,[],[f43])).
% 11.19/1.97  
% 11.19/1.97  fof(f78,plain,(
% 11.19/1.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(cnf_transformation,[],[f23])).
% 11.19/1.97  
% 11.19/1.97  fof(f104,plain,(
% 11.19/1.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(definition_unfolding,[],[f78,f70])).
% 11.19/1.97  
% 11.19/1.97  fof(f79,plain,(
% 11.19/1.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(cnf_transformation,[],[f23])).
% 11.19/1.97  
% 11.19/1.97  fof(f103,plain,(
% 11.19/1.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(definition_unfolding,[],[f79,f70])).
% 11.19/1.97  
% 11.19/1.97  fof(f53,plain,(
% 11.19/1.97    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 11.19/1.97    inference(cnf_transformation,[],[f34])).
% 11.19/1.97  
% 11.19/1.97  fof(f116,plain,(
% 11.19/1.97    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 11.19/1.97    inference(equality_resolution,[],[f53])).
% 11.19/1.97  
% 11.19/1.97  fof(f75,plain,(
% 11.19/1.97    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(cnf_transformation,[],[f40])).
% 11.19/1.97  
% 11.19/1.97  fof(f100,plain,(
% 11.19/1.97    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(definition_unfolding,[],[f75,f69])).
% 11.19/1.97  
% 11.19/1.97  fof(f56,plain,(
% 11.19/1.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.19/1.97    inference(cnf_transformation,[],[f34])).
% 11.19/1.97  
% 11.19/1.97  fof(f110,plain,(
% 11.19/1.97    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 11.19/1.97    inference(equality_resolution,[],[f56])).
% 11.19/1.97  
% 11.19/1.97  fof(f111,plain,(
% 11.19/1.97    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 11.19/1.97    inference(equality_resolution,[],[f110])).
% 11.19/1.97  
% 11.19/1.97  fof(f86,plain,(
% 11.19/1.97    k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6),
% 11.19/1.97    inference(cnf_transformation,[],[f43])).
% 11.19/1.97  
% 11.19/1.97  fof(f16,axiom,(
% 11.19/1.97    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f80,plain,(
% 11.19/1.97    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 11.19/1.97    inference(cnf_transformation,[],[f16])).
% 11.19/1.97  
% 11.19/1.97  fof(f12,axiom,(
% 11.19/1.97    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 11.19/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.19/1.97  
% 11.19/1.97  fof(f20,plain,(
% 11.19/1.97    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 11.19/1.97    inference(ennf_transformation,[],[f12])).
% 11.19/1.97  
% 11.19/1.97  fof(f72,plain,(
% 11.19/1.97    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 11.19/1.97    inference(cnf_transformation,[],[f20])).
% 11.19/1.97  
% 11.19/1.97  fof(f118,plain,(
% 11.19/1.97    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 11.19/1.97    inference(equality_resolution,[],[f72])).
% 11.19/1.97  
% 11.19/1.97  fof(f81,plain,(
% 11.19/1.97    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 11.19/1.97    inference(cnf_transformation,[],[f16])).
% 11.19/1.97  
% 11.19/1.97  fof(f74,plain,(
% 11.19/1.97    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(cnf_transformation,[],[f40])).
% 11.19/1.97  
% 11.19/1.97  fof(f101,plain,(
% 11.19/1.97    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 11.19/1.97    inference(definition_unfolding,[],[f74,f69])).
% 11.19/1.97  
% 11.19/1.97  cnf(c_26,plain,
% 11.19/1.97      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 11.19/1.97      inference(cnf_transformation,[],[f73]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_698,plain,
% 11.19/1.97      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_6,plain,
% 11.19/1.97      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.19/1.97      inference(cnf_transformation,[],[f50]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_4,plain,
% 11.19/1.97      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 11.19/1.97      inference(cnf_transformation,[],[f108]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_716,plain,
% 11.19/1.97      ( r2_hidden(X0,X1) = iProver_top
% 11.19/1.97      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_2496,plain,
% 11.19/1.97      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
% 11.19/1.97      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_6,c_716]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_7,plain,
% 11.19/1.97      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.19/1.97      inference(cnf_transformation,[],[f52]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_17,plain,
% 11.19/1.97      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) ),
% 11.19/1.97      inference(cnf_transformation,[],[f117]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_705,plain,
% 11.19/1.97      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) != iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_2152,plain,
% 11.19/1.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_7,c_705]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_2778,plain,
% 11.19/1.97      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
% 11.19/1.97      inference(global_propositional_subsumption,[status(thm)],[c_2496,c_2152]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_2785,plain,
% 11.19/1.97      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_698,c_2778]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_16,plain,
% 11.19/1.97      ( ~ r2_hidden(X0,X1)
% 11.19/1.97      | r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
% 11.19/1.97      | X2 = X0 ),
% 11.19/1.97      inference(cnf_transformation,[],[f94]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_706,plain,
% 11.19/1.97      ( X0 = X1
% 11.19/1.97      | r2_hidden(X1,X2) != iProver_top
% 11.19/1.97      | r2_hidden(X1,k4_xboole_0(X2,k1_enumset1(X0,X0,X0))) = iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_4362,plain,
% 11.19/1.97      ( X0 = X1
% 11.19/1.97      | r2_hidden(X1,k1_enumset1(X0,X0,X0)) != iProver_top
% 11.19/1.97      | r2_hidden(X1,k1_xboole_0) = iProver_top ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_2785,c_706]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_10473,plain,
% 11.19/1.97      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 11.19/1.97      inference(forward_subsumption_resolution,[status(thm)],[c_4362,c_2152]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_10485,plain,
% 11.19/1.97      ( k1_enumset1(X0,X0,X0) = k1_xboole_0 | sK2(k1_enumset1(X0,X0,X0)) = X0 ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_698,c_10473]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_21,plain,
% 11.19/1.97      ( ~ r2_hidden(X0,X1)
% 11.19/1.97      | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_enumset1(X0,X0,X2) ),
% 11.19/1.97      inference(cnf_transformation,[],[f99]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_701,plain,
% 11.19/1.97      ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)
% 11.19/1.97      | r2_hidden(X0,X2) != iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_3585,plain,
% 11.19/1.97      ( k1_enumset1(X0,X0,X1) != k1_xboole_0
% 11.19/1.97      | r2_hidden(X0,k1_enumset1(X0,X0,X1)) != iProver_top ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_2785,c_701]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_14,plain,
% 11.19/1.97      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 11.19/1.97      inference(cnf_transformation,[],[f115]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_708,plain,
% 11.19/1.97      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_3770,plain,
% 11.19/1.97      ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
% 11.19/1.97      inference(forward_subsumption_resolution,[status(thm)],[c_3585,c_708]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_11840,plain,
% 11.19/1.97      ( sK2(k1_enumset1(X0,X0,X0)) = X0 ),
% 11.19/1.97      inference(forward_subsumption_resolution,[status(thm)],[c_10485,c_3770]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_34,negated_conjecture,
% 11.19/1.97      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 11.19/1.97      inference(cnf_transformation,[],[f106]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_693,plain,
% 11.19/1.97      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_27,plain,
% 11.19/1.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 11.19/1.97      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 11.19/1.97      | k1_xboole_0 = X1
% 11.19/1.97      | k1_xboole_0 = X2
% 11.19/1.97      | k1_xboole_0 = X3 ),
% 11.19/1.97      inference(cnf_transformation,[],[f102]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_697,plain,
% 11.19/1.97      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 11.19/1.97      | k1_xboole_0 = X0
% 11.19/1.97      | k1_xboole_0 = X1
% 11.19/1.97      | k1_xboole_0 = X2
% 11.19/1.97      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_6527,plain,
% 11.19/1.97      ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
% 11.19/1.97      | sK5 = k1_xboole_0
% 11.19/1.97      | sK4 = k1_xboole_0
% 11.19/1.97      | sK3 = k1_xboole_0 ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_693,c_697]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_30,plain,
% 11.19/1.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 11.19/1.97      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 11.19/1.97      | k1_xboole_0 = X1
% 11.19/1.97      | k1_xboole_0 = X2
% 11.19/1.97      | k1_xboole_0 = X3 ),
% 11.19/1.97      inference(cnf_transformation,[],[f105]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_694,plain,
% 11.19/1.97      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 11.19/1.97      | k1_xboole_0 = X0
% 11.19/1.97      | k1_xboole_0 = X1
% 11.19/1.97      | k1_xboole_0 = X2
% 11.19/1.97      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_1151,plain,
% 11.19/1.97      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 11.19/1.97      | sK5 = k1_xboole_0
% 11.19/1.97      | sK4 = k1_xboole_0
% 11.19/1.97      | sK3 = k1_xboole_0 ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_693,c_694]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_37,negated_conjecture,
% 11.19/1.97      ( k1_xboole_0 != sK3 ),
% 11.19/1.97      inference(cnf_transformation,[],[f82]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_36,negated_conjecture,
% 11.19/1.97      ( k1_xboole_0 != sK4 ),
% 11.19/1.97      inference(cnf_transformation,[],[f83]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_35,negated_conjecture,
% 11.19/1.97      ( k1_xboole_0 != sK5 ),
% 11.19/1.97      inference(cnf_transformation,[],[f84]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_1090,plain,
% 11.19/1.97      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
% 11.19/1.97      | k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 11.19/1.97      | k1_xboole_0 = sK5
% 11.19/1.97      | k1_xboole_0 = sK4
% 11.19/1.97      | k1_xboole_0 = sK3 ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_30]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_1493,plain,
% 11.19/1.97      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
% 11.19/1.97      inference(global_propositional_subsumption,
% 11.19/1.97                [status(thm)],
% 11.19/1.97                [c_1151,c_37,c_36,c_35,c_34,c_1090]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_29,plain,
% 11.19/1.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 11.19/1.97      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 11.19/1.97      | k1_xboole_0 = X1
% 11.19/1.97      | k1_xboole_0 = X2
% 11.19/1.97      | k1_xboole_0 = X3 ),
% 11.19/1.97      inference(cnf_transformation,[],[f104]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_695,plain,
% 11.19/1.97      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 11.19/1.97      | k1_xboole_0 = X0
% 11.19/1.97      | k1_xboole_0 = X1
% 11.19/1.97      | k1_xboole_0 = X2
% 11.19/1.97      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_2512,plain,
% 11.19/1.97      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 11.19/1.97      | sK5 = k1_xboole_0
% 11.19/1.97      | sK4 = k1_xboole_0
% 11.19/1.97      | sK3 = k1_xboole_0 ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_693,c_695]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_1087,plain,
% 11.19/1.97      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
% 11.19/1.97      | k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 11.19/1.97      | k1_xboole_0 = sK5
% 11.19/1.97      | k1_xboole_0 = sK4
% 11.19/1.97      | k1_xboole_0 = sK3 ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_29]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_3576,plain,
% 11.19/1.97      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
% 11.19/1.97      inference(global_propositional_subsumption,
% 11.19/1.97                [status(thm)],
% 11.19/1.97                [c_2512,c_37,c_36,c_35,c_34,c_1087]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_28,plain,
% 11.19/1.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 11.19/1.97      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 11.19/1.97      | k1_xboole_0 = X1
% 11.19/1.97      | k1_xboole_0 = X2
% 11.19/1.97      | k1_xboole_0 = X3 ),
% 11.19/1.97      inference(cnf_transformation,[],[f103]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_696,plain,
% 11.19/1.97      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 11.19/1.97      | k1_xboole_0 = X0
% 11.19/1.97      | k1_xboole_0 = X1
% 11.19/1.97      | k1_xboole_0 = X2
% 11.19/1.97      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_4356,plain,
% 11.19/1.97      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
% 11.19/1.97      | sK5 = k1_xboole_0
% 11.19/1.97      | sK4 = k1_xboole_0
% 11.19/1.97      | sK3 = k1_xboole_0 ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_693,c_696]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_1084,plain,
% 11.19/1.97      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
% 11.19/1.97      | k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
% 11.19/1.97      | k1_xboole_0 = sK5
% 11.19/1.97      | k1_xboole_0 = sK4
% 11.19/1.97      | k1_xboole_0 = sK3 ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_28]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_5000,plain,
% 11.19/1.97      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
% 11.19/1.97      inference(global_propositional_subsumption,
% 11.19/1.97                [status(thm)],
% 11.19/1.97                [c_4356,c_37,c_36,c_35,c_34,c_1084]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_6528,plain,
% 11.19/1.97      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6
% 11.19/1.97      | sK5 = k1_xboole_0
% 11.19/1.97      | sK4 = k1_xboole_0
% 11.19/1.97      | sK3 = k1_xboole_0 ),
% 11.19/1.97      inference(light_normalisation,
% 11.19/1.97                [status(thm)],
% 11.19/1.97                [c_6527,c_1493,c_3576,c_5000]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_15,plain,
% 11.19/1.97      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3)) | X0 = X1 | X0 = X2 | X0 = X3 ),
% 11.19/1.97      inference(cnf_transformation,[],[f116]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_79,plain,
% 11.19/1.97      ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 11.19/1.97      | k1_xboole_0 = k1_xboole_0 ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_15]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_82,plain,
% 11.19/1.97      ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_14]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_270,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_997,plain,
% 11.19/1.97      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_270]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_998,plain,
% 11.19/1.97      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_997]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_999,plain,
% 11.19/1.97      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_270]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_1000,plain,
% 11.19/1.97      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_999]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_1001,plain,
% 11.19/1.97      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_270]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_1002,plain,
% 11.19/1.97      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 11.19/1.97      inference(instantiation,[status(thm)],[c_1001]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_7241,plain,
% 11.19/1.97      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
% 11.19/1.97      inference(global_propositional_subsumption,
% 11.19/1.97                [status(thm)],
% 11.19/1.97                [c_6528,c_37,c_36,c_35,c_79,c_82,c_998,c_1000,c_1002]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_24,plain,
% 11.19/1.97      ( ~ r2_hidden(X0,X1)
% 11.19/1.97      | k4_tarski(k4_tarski(X2,X0),X3) != sK2(X1)
% 11.19/1.97      | k1_xboole_0 = X1 ),
% 11.19/1.97      inference(cnf_transformation,[],[f100]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_700,plain,
% 11.19/1.97      ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
% 11.19/1.97      | k1_xboole_0 = X3
% 11.19/1.97      | r2_hidden(X1,X3) != iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_7250,plain,
% 11.19/1.97      ( sK2(X0) != sK6
% 11.19/1.97      | k1_xboole_0 = X0
% 11.19/1.97      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_7241,c_700]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_11847,plain,
% 11.19/1.97      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 11.19/1.97      | sK6 != X0
% 11.19/1.97      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_11840,c_7250]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_12640,plain,
% 11.19/1.97      ( sK6 != X0
% 11.19/1.97      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 11.19/1.97      inference(forward_subsumption_resolution,[status(thm)],[c_11847,c_3770]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_12644,plain,
% 11.19/1.97      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
% 11.19/1.97      inference(equality_resolution,[status(thm)],[c_12640]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_12,plain,
% 11.19/1.97      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 11.19/1.97      inference(cnf_transformation,[],[f111]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_710,plain,
% 11.19/1.97      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) = iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_33,negated_conjecture,
% 11.19/1.97      ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 11.19/1.97      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 11.19/1.97      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
% 11.19/1.97      inference(cnf_transformation,[],[f86]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_5003,plain,
% 11.19/1.97      ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 11.19/1.97      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 11.19/1.97      | k2_mcart_1(sK6) = sK6 ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_33,c_5000]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_5005,plain,
% 11.19/1.97      ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
% 11.19/1.97      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 11.19/1.97      | k2_mcart_1(sK6) = sK6 ),
% 11.19/1.97      inference(demodulation,[status(thm)],[c_5003,c_1493,c_3576]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_32,plain,
% 11.19/1.97      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 11.19/1.97      inference(cnf_transformation,[],[f80]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_7249,plain,
% 11.19/1.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_7241,c_32]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_7953,plain,
% 11.19/1.97      ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 11.19/1.97      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 11.19/1.97      | k2_mcart_1(sK6) = sK6 ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_5005,c_7249]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_7265,plain,
% 11.19/1.97      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 11.19/1.97      inference(demodulation,[status(thm)],[c_7249,c_7241]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_22,plain,
% 11.19/1.97      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 11.19/1.97      inference(cnf_transformation,[],[f118]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_31,plain,
% 11.19/1.97      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 11.19/1.97      inference(cnf_transformation,[],[f81]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_746,plain,
% 11.19/1.97      ( k4_tarski(X0,X1) != X1 ),
% 11.19/1.97      inference(light_normalisation,[status(thm)],[c_22,c_31]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_7274,plain,
% 11.19/1.97      ( k2_mcart_1(sK6) != sK6 ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_7265,c_746]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_8111,plain,
% 11.19/1.97      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 11.19/1.97      | k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 11.19/1.97      inference(global_propositional_subsumption,[status(thm)],[c_7953,c_7274]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_8112,plain,
% 11.19/1.97      ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 11.19/1.97      | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 11.19/1.97      inference(renaming,[status(thm)],[c_8111]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_25,plain,
% 11.19/1.97      ( ~ r2_hidden(X0,X1)
% 11.19/1.97      | k4_tarski(k4_tarski(X0,X2),X3) != sK2(X1)
% 11.19/1.97      | k1_xboole_0 = X1 ),
% 11.19/1.97      inference(cnf_transformation,[],[f101]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_699,plain,
% 11.19/1.97      ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
% 11.19/1.97      | k1_xboole_0 = X3
% 11.19/1.97      | r2_hidden(X0,X3) != iProver_top ),
% 11.19/1.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_7273,plain,
% 11.19/1.97      ( k4_tarski(sK6,X0) != sK2(X1)
% 11.19/1.97      | k1_xboole_0 = X1
% 11.19/1.97      | r2_hidden(k1_mcart_1(sK6),X1) != iProver_top ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_7265,c_699]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_9805,plain,
% 11.19/1.97      ( sK2(X0) != k1_mcart_1(sK6)
% 11.19/1.97      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 11.19/1.97      | k1_xboole_0 = X0
% 11.19/1.97      | r2_hidden(k1_mcart_1(sK6),X0) != iProver_top ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_8112,c_7273]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_11844,plain,
% 11.19/1.97      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 11.19/1.97      | k1_mcart_1(sK6) != X0
% 11.19/1.97      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 11.19/1.97      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_11840,c_9805]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_12651,plain,
% 11.19/1.97      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 11.19/1.97      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 11.19/1.97      inference(forward_subsumption_resolution,
% 11.19/1.97                [status(thm)],
% 11.19/1.97                [c_11844,c_10473,c_3770]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_12656,plain,
% 11.19/1.97      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 11.19/1.97      inference(superposition,[status(thm)],[c_710,c_12651]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_34343,plain,
% 11.19/1.97      ( r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
% 11.19/1.97      inference(light_normalisation,[status(thm)],[c_12644,c_12656]) ).
% 11.19/1.97  
% 11.19/1.97  cnf(c_34345,plain,
% 11.19/1.97      ( $false ),
% 11.19/1.97      inference(forward_subsumption_resolution,[status(thm)],[c_34343,c_708]) ).
% 11.19/1.97  
% 11.19/1.97  
% 11.19/1.97  % SZS output end CNFRefutation for theBenchmark.p
% 11.19/1.97  
% 11.19/1.97  ------                               Statistics
% 11.19/1.97  
% 11.19/1.97  ------ Selected
% 11.19/1.97  
% 11.19/1.97  total_time:                             1.071
% 11.19/1.97  
%------------------------------------------------------------------------------
