%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:50 EST 2020

% Result     : Theorem 8.19s
% Output     : CNFRefutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 552 expanded)
%              Number of clauses        :   50 ( 102 expanded)
%              Number of leaves         :   17 ( 164 expanded)
%              Depth                    :   21
%              Number of atoms          :  329 (1316 expanded)
%              Number of equality atoms :  232 (1060 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK4,sK5) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK3) = sK3
        | k1_mcart_1(sK3) = sK3 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK3 ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( k2_mcart_1(sK3) = sK3
      | k1_mcart_1(sK3) = sK3 )
    & k4_tarski(sK4,sK5) = sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f32,f31])).

fof(f61,plain,
    ( k2_mcart_1(sK3) = sK3
    | k1_mcart_1(sK3) = sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    k4_tarski(sK4,sK5) = sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f74,plain,(
    ! [X0,X1] : k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f54,f63,f63,f63])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f39,f62])).

fof(f80,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f72])).

fof(f81,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f80])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f29])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f34,f63])).

fof(f77,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f59,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f35,f63])).

fof(f75,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f66])).

fof(f76,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f75])).

cnf(c_23,negated_conjecture,
    ( k1_mcart_1(sK3) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( k4_tarski(sK4,sK5) = sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_830,plain,
    ( k1_mcart_1(sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_24,c_19])).

cnf(c_832,plain,
    ( k2_mcart_1(sK3) = sK3
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_23,c_830])).

cnf(c_18,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_644,plain,
    ( k2_mcart_1(sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_24,c_18])).

cnf(c_834,plain,
    ( sK5 = sK3
    | sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_832,c_644])).

cnf(c_1475,plain,
    ( k4_tarski(sK4,sK3) = sK3
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_834,c_24])).

cnf(c_17,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_485,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2375,plain,
    ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_485])).

cnf(c_4339,plain,
    ( sK4 = sK3
    | r2_hidden(sK3,k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_2375])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_482,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3583,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r2_hidden(sK3,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_482])).

cnf(c_5895,plain,
    ( sK4 = sK3
    | r2_hidden(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_3583])).

cnf(c_22,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_477,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1034,plain,
    ( k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_24,c_17])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_490,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2698,plain,
    ( k4_tarski(X0,X1) = X2
    | r2_hidden(X2,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_490])).

cnf(c_6542,plain,
    ( k4_tarski(sK4,sK5) = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_2698])).

cnf(c_6562,plain,
    ( sK3 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6542,c_24])).

cnf(c_6611,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK2(k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_477,c_6562])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X2,X0) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_479,plain,
    ( k4_tarski(X0,X1) != sK2(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2355,plain,
    ( sK2(X0) != sK3
    | k1_xboole_0 = X0
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_479])).

cnf(c_7810,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | r2_hidden(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6611,c_2355])).

cnf(c_7853,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_5895,c_7810])).

cnf(c_27403,plain,
    ( sK4 = sK3
    | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7853,c_5895])).

cnf(c_13,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_480,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1040,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_480])).

cnf(c_28081,plain,
    ( sK4 = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27403,c_1040])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X0,X2) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_478,plain,
    ( k4_tarski(X0,X1) != sK2(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_913,plain,
    ( sK2(X0) != sK3
    | k1_xboole_0 = X0
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_478])).

cnf(c_7812,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6611,c_913])).

cnf(c_28101,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28081,c_7812])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_10045,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_10046,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10045])).

cnf(c_32278,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28101,c_10046])).

cnf(c_32365,plain,
    ( r2_hidden(k4_tarski(X0,sK3),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_32278,c_2375])).

cnf(c_32409,plain,
    ( r2_hidden(k4_tarski(X0,sK3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32365,c_13])).

cnf(c_32942,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_32409,c_1040])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.19/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/1.53  
% 8.19/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.19/1.53  
% 8.19/1.53  ------  iProver source info
% 8.19/1.53  
% 8.19/1.53  git: date: 2020-06-30 10:37:57 +0100
% 8.19/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.19/1.53  git: non_committed_changes: false
% 8.19/1.53  git: last_make_outside_of_git: false
% 8.19/1.53  
% 8.19/1.53  ------ 
% 8.19/1.53  
% 8.19/1.53  ------ Input Options
% 8.19/1.53  
% 8.19/1.53  --out_options                           all
% 8.19/1.53  --tptp_safe_out                         true
% 8.19/1.53  --problem_path                          ""
% 8.19/1.53  --include_path                          ""
% 8.19/1.53  --clausifier                            res/vclausify_rel
% 8.19/1.53  --clausifier_options                    --mode clausify
% 8.19/1.53  --stdin                                 false
% 8.19/1.53  --stats_out                             all
% 8.19/1.53  
% 8.19/1.53  ------ General Options
% 8.19/1.53  
% 8.19/1.53  --fof                                   false
% 8.19/1.53  --time_out_real                         305.
% 8.19/1.53  --time_out_virtual                      -1.
% 8.19/1.53  --symbol_type_check                     false
% 8.19/1.53  --clausify_out                          false
% 8.19/1.53  --sig_cnt_out                           false
% 8.19/1.53  --trig_cnt_out                          false
% 8.19/1.53  --trig_cnt_out_tolerance                1.
% 8.19/1.53  --trig_cnt_out_sk_spl                   false
% 8.19/1.53  --abstr_cl_out                          false
% 8.19/1.53  
% 8.19/1.53  ------ Global Options
% 8.19/1.53  
% 8.19/1.53  --schedule                              default
% 8.19/1.53  --add_important_lit                     false
% 8.19/1.53  --prop_solver_per_cl                    1000
% 8.19/1.53  --min_unsat_core                        false
% 8.19/1.53  --soft_assumptions                      false
% 8.19/1.53  --soft_lemma_size                       3
% 8.19/1.53  --prop_impl_unit_size                   0
% 8.19/1.53  --prop_impl_unit                        []
% 8.19/1.53  --share_sel_clauses                     true
% 8.19/1.53  --reset_solvers                         false
% 8.19/1.53  --bc_imp_inh                            [conj_cone]
% 8.19/1.53  --conj_cone_tolerance                   3.
% 8.19/1.53  --extra_neg_conj                        none
% 8.19/1.53  --large_theory_mode                     true
% 8.19/1.53  --prolific_symb_bound                   200
% 8.19/1.53  --lt_threshold                          2000
% 8.19/1.53  --clause_weak_htbl                      true
% 8.19/1.53  --gc_record_bc_elim                     false
% 8.19/1.53  
% 8.19/1.53  ------ Preprocessing Options
% 8.19/1.53  
% 8.19/1.53  --preprocessing_flag                    true
% 8.19/1.53  --time_out_prep_mult                    0.1
% 8.19/1.53  --splitting_mode                        input
% 8.19/1.53  --splitting_grd                         true
% 8.19/1.53  --splitting_cvd                         false
% 8.19/1.53  --splitting_cvd_svl                     false
% 8.19/1.53  --splitting_nvd                         32
% 8.19/1.53  --sub_typing                            true
% 8.19/1.53  --prep_gs_sim                           true
% 8.19/1.53  --prep_unflatten                        true
% 8.19/1.53  --prep_res_sim                          true
% 8.19/1.53  --prep_upred                            true
% 8.19/1.53  --prep_sem_filter                       exhaustive
% 8.19/1.53  --prep_sem_filter_out                   false
% 8.19/1.53  --pred_elim                             true
% 8.19/1.53  --res_sim_input                         true
% 8.19/1.53  --eq_ax_congr_red                       true
% 8.19/1.53  --pure_diseq_elim                       true
% 8.19/1.53  --brand_transform                       false
% 8.19/1.53  --non_eq_to_eq                          false
% 8.19/1.53  --prep_def_merge                        true
% 8.19/1.53  --prep_def_merge_prop_impl              false
% 8.19/1.53  --prep_def_merge_mbd                    true
% 8.19/1.53  --prep_def_merge_tr_red                 false
% 8.19/1.53  --prep_def_merge_tr_cl                  false
% 8.19/1.53  --smt_preprocessing                     true
% 8.19/1.53  --smt_ac_axioms                         fast
% 8.19/1.53  --preprocessed_out                      false
% 8.19/1.53  --preprocessed_stats                    false
% 8.19/1.53  
% 8.19/1.53  ------ Abstraction refinement Options
% 8.19/1.53  
% 8.19/1.53  --abstr_ref                             []
% 8.19/1.53  --abstr_ref_prep                        false
% 8.19/1.53  --abstr_ref_until_sat                   false
% 8.19/1.53  --abstr_ref_sig_restrict                funpre
% 8.19/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 8.19/1.53  --abstr_ref_under                       []
% 8.19/1.53  
% 8.19/1.53  ------ SAT Options
% 8.19/1.53  
% 8.19/1.53  --sat_mode                              false
% 8.19/1.53  --sat_fm_restart_options                ""
% 8.19/1.53  --sat_gr_def                            false
% 8.19/1.53  --sat_epr_types                         true
% 8.19/1.53  --sat_non_cyclic_types                  false
% 8.19/1.53  --sat_finite_models                     false
% 8.19/1.53  --sat_fm_lemmas                         false
% 8.19/1.53  --sat_fm_prep                           false
% 8.19/1.53  --sat_fm_uc_incr                        true
% 8.19/1.53  --sat_out_model                         small
% 8.19/1.53  --sat_out_clauses                       false
% 8.19/1.53  
% 8.19/1.53  ------ QBF Options
% 8.19/1.53  
% 8.19/1.53  --qbf_mode                              false
% 8.19/1.53  --qbf_elim_univ                         false
% 8.19/1.53  --qbf_dom_inst                          none
% 8.19/1.53  --qbf_dom_pre_inst                      false
% 8.19/1.53  --qbf_sk_in                             false
% 8.19/1.53  --qbf_pred_elim                         true
% 8.19/1.53  --qbf_split                             512
% 8.19/1.53  
% 8.19/1.53  ------ BMC1 Options
% 8.19/1.53  
% 8.19/1.53  --bmc1_incremental                      false
% 8.19/1.53  --bmc1_axioms                           reachable_all
% 8.19/1.53  --bmc1_min_bound                        0
% 8.19/1.53  --bmc1_max_bound                        -1
% 8.19/1.53  --bmc1_max_bound_default                -1
% 8.19/1.53  --bmc1_symbol_reachability              true
% 8.19/1.53  --bmc1_property_lemmas                  false
% 8.19/1.53  --bmc1_k_induction                      false
% 8.19/1.53  --bmc1_non_equiv_states                 false
% 8.19/1.53  --bmc1_deadlock                         false
% 8.19/1.53  --bmc1_ucm                              false
% 8.19/1.53  --bmc1_add_unsat_core                   none
% 8.19/1.53  --bmc1_unsat_core_children              false
% 8.19/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 8.19/1.53  --bmc1_out_stat                         full
% 8.19/1.53  --bmc1_ground_init                      false
% 8.19/1.53  --bmc1_pre_inst_next_state              false
% 8.19/1.53  --bmc1_pre_inst_state                   false
% 8.19/1.53  --bmc1_pre_inst_reach_state             false
% 8.19/1.53  --bmc1_out_unsat_core                   false
% 8.19/1.53  --bmc1_aig_witness_out                  false
% 8.19/1.53  --bmc1_verbose                          false
% 8.19/1.53  --bmc1_dump_clauses_tptp                false
% 8.19/1.53  --bmc1_dump_unsat_core_tptp             false
% 8.19/1.53  --bmc1_dump_file                        -
% 8.19/1.53  --bmc1_ucm_expand_uc_limit              128
% 8.19/1.53  --bmc1_ucm_n_expand_iterations          6
% 8.19/1.53  --bmc1_ucm_extend_mode                  1
% 8.19/1.53  --bmc1_ucm_init_mode                    2
% 8.19/1.53  --bmc1_ucm_cone_mode                    none
% 8.19/1.53  --bmc1_ucm_reduced_relation_type        0
% 8.19/1.53  --bmc1_ucm_relax_model                  4
% 8.19/1.53  --bmc1_ucm_full_tr_after_sat            true
% 8.19/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 8.19/1.53  --bmc1_ucm_layered_model                none
% 8.19/1.53  --bmc1_ucm_max_lemma_size               10
% 8.19/1.53  
% 8.19/1.53  ------ AIG Options
% 8.19/1.53  
% 8.19/1.53  --aig_mode                              false
% 8.19/1.53  
% 8.19/1.53  ------ Instantiation Options
% 8.19/1.53  
% 8.19/1.53  --instantiation_flag                    true
% 8.19/1.53  --inst_sos_flag                         false
% 8.19/1.53  --inst_sos_phase                        true
% 8.19/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.19/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.19/1.53  --inst_lit_sel_side                     num_symb
% 8.19/1.53  --inst_solver_per_active                1400
% 8.19/1.53  --inst_solver_calls_frac                1.
% 8.19/1.53  --inst_passive_queue_type               priority_queues
% 8.19/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.19/1.53  --inst_passive_queues_freq              [25;2]
% 8.19/1.53  --inst_dismatching                      true
% 8.19/1.53  --inst_eager_unprocessed_to_passive     true
% 8.19/1.53  --inst_prop_sim_given                   true
% 8.19/1.53  --inst_prop_sim_new                     false
% 8.19/1.53  --inst_subs_new                         false
% 8.19/1.53  --inst_eq_res_simp                      false
% 8.19/1.53  --inst_subs_given                       false
% 8.19/1.53  --inst_orphan_elimination               true
% 8.19/1.53  --inst_learning_loop_flag               true
% 8.19/1.53  --inst_learning_start                   3000
% 8.19/1.53  --inst_learning_factor                  2
% 8.19/1.53  --inst_start_prop_sim_after_learn       3
% 8.19/1.53  --inst_sel_renew                        solver
% 8.19/1.53  --inst_lit_activity_flag                true
% 8.19/1.53  --inst_restr_to_given                   false
% 8.19/1.53  --inst_activity_threshold               500
% 8.19/1.53  --inst_out_proof                        true
% 8.19/1.53  
% 8.19/1.53  ------ Resolution Options
% 8.19/1.53  
% 8.19/1.53  --resolution_flag                       true
% 8.19/1.53  --res_lit_sel                           adaptive
% 8.19/1.53  --res_lit_sel_side                      none
% 8.19/1.53  --res_ordering                          kbo
% 8.19/1.53  --res_to_prop_solver                    active
% 8.19/1.53  --res_prop_simpl_new                    false
% 8.19/1.53  --res_prop_simpl_given                  true
% 8.19/1.53  --res_passive_queue_type                priority_queues
% 8.19/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.19/1.53  --res_passive_queues_freq               [15;5]
% 8.19/1.53  --res_forward_subs                      full
% 8.19/1.53  --res_backward_subs                     full
% 8.19/1.53  --res_forward_subs_resolution           true
% 8.19/1.53  --res_backward_subs_resolution          true
% 8.19/1.53  --res_orphan_elimination                true
% 8.19/1.53  --res_time_limit                        2.
% 8.19/1.53  --res_out_proof                         true
% 8.19/1.53  
% 8.19/1.53  ------ Superposition Options
% 8.19/1.53  
% 8.19/1.53  --superposition_flag                    true
% 8.19/1.53  --sup_passive_queue_type                priority_queues
% 8.19/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.19/1.53  --sup_passive_queues_freq               [8;1;4]
% 8.19/1.53  --demod_completeness_check              fast
% 8.19/1.53  --demod_use_ground                      true
% 8.19/1.53  --sup_to_prop_solver                    passive
% 8.19/1.53  --sup_prop_simpl_new                    true
% 8.19/1.53  --sup_prop_simpl_given                  true
% 8.19/1.53  --sup_fun_splitting                     false
% 8.19/1.53  --sup_smt_interval                      50000
% 8.19/1.53  
% 8.19/1.53  ------ Superposition Simplification Setup
% 8.19/1.53  
% 8.19/1.53  --sup_indices_passive                   []
% 8.19/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.19/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.19/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.19/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 8.19/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.19/1.53  --sup_full_bw                           [BwDemod]
% 8.19/1.53  --sup_immed_triv                        [TrivRules]
% 8.19/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.19/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.19/1.53  --sup_immed_bw_main                     []
% 8.19/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.19/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 8.19/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.19/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.19/1.53  
% 8.19/1.53  ------ Combination Options
% 8.19/1.53  
% 8.19/1.53  --comb_res_mult                         3
% 8.19/1.53  --comb_sup_mult                         2
% 8.19/1.53  --comb_inst_mult                        10
% 8.19/1.53  
% 8.19/1.53  ------ Debug Options
% 8.19/1.53  
% 8.19/1.53  --dbg_backtrace                         false
% 8.19/1.53  --dbg_dump_prop_clauses                 false
% 8.19/1.53  --dbg_dump_prop_clauses_file            -
% 8.19/1.53  --dbg_out_stat                          false
% 8.19/1.53  ------ Parsing...
% 8.19/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.19/1.53  
% 8.19/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.19/1.53  
% 8.19/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.19/1.53  
% 8.19/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.19/1.53  ------ Proving...
% 8.19/1.53  ------ Problem Properties 
% 8.19/1.53  
% 8.19/1.53  
% 8.19/1.53  clauses                                 25
% 8.19/1.53  conjectures                             2
% 8.19/1.53  EPR                                     0
% 8.19/1.53  Horn                                    19
% 8.19/1.53  unary                                   10
% 8.19/1.53  binary                                  5
% 8.19/1.53  lits                                    51
% 8.19/1.53  lits eq                                 30
% 8.19/1.53  fd_pure                                 0
% 8.19/1.53  fd_pseudo                               0
% 8.19/1.53  fd_cond                                 4
% 8.19/1.53  fd_pseudo_cond                          5
% 8.19/1.53  AC symbols                              0
% 8.19/1.53  
% 8.19/1.53  ------ Schedule dynamic 5 is on 
% 8.19/1.53  
% 8.19/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.19/1.53  
% 8.19/1.53  
% 8.19/1.53  ------ 
% 8.19/1.53  Current options:
% 8.19/1.53  ------ 
% 8.19/1.53  
% 8.19/1.53  ------ Input Options
% 8.19/1.53  
% 8.19/1.53  --out_options                           all
% 8.19/1.53  --tptp_safe_out                         true
% 8.19/1.53  --problem_path                          ""
% 8.19/1.53  --include_path                          ""
% 8.19/1.53  --clausifier                            res/vclausify_rel
% 8.19/1.53  --clausifier_options                    --mode clausify
% 8.19/1.53  --stdin                                 false
% 8.19/1.53  --stats_out                             all
% 8.19/1.53  
% 8.19/1.53  ------ General Options
% 8.19/1.53  
% 8.19/1.53  --fof                                   false
% 8.19/1.53  --time_out_real                         305.
% 8.19/1.53  --time_out_virtual                      -1.
% 8.19/1.53  --symbol_type_check                     false
% 8.19/1.53  --clausify_out                          false
% 8.19/1.53  --sig_cnt_out                           false
% 8.19/1.53  --trig_cnt_out                          false
% 8.19/1.53  --trig_cnt_out_tolerance                1.
% 8.19/1.53  --trig_cnt_out_sk_spl                   false
% 8.19/1.53  --abstr_cl_out                          false
% 8.19/1.53  
% 8.19/1.53  ------ Global Options
% 8.19/1.53  
% 8.19/1.53  --schedule                              default
% 8.19/1.53  --add_important_lit                     false
% 8.19/1.53  --prop_solver_per_cl                    1000
% 8.19/1.53  --min_unsat_core                        false
% 8.19/1.53  --soft_assumptions                      false
% 8.19/1.53  --soft_lemma_size                       3
% 8.19/1.53  --prop_impl_unit_size                   0
% 8.19/1.53  --prop_impl_unit                        []
% 8.19/1.53  --share_sel_clauses                     true
% 8.19/1.53  --reset_solvers                         false
% 8.19/1.53  --bc_imp_inh                            [conj_cone]
% 8.19/1.53  --conj_cone_tolerance                   3.
% 8.19/1.53  --extra_neg_conj                        none
% 8.19/1.53  --large_theory_mode                     true
% 8.19/1.53  --prolific_symb_bound                   200
% 8.19/1.53  --lt_threshold                          2000
% 8.19/1.53  --clause_weak_htbl                      true
% 8.19/1.53  --gc_record_bc_elim                     false
% 8.19/1.53  
% 8.19/1.53  ------ Preprocessing Options
% 8.19/1.53  
% 8.19/1.53  --preprocessing_flag                    true
% 8.19/1.53  --time_out_prep_mult                    0.1
% 8.19/1.53  --splitting_mode                        input
% 8.19/1.53  --splitting_grd                         true
% 8.19/1.53  --splitting_cvd                         false
% 8.19/1.53  --splitting_cvd_svl                     false
% 8.19/1.53  --splitting_nvd                         32
% 8.19/1.53  --sub_typing                            true
% 8.19/1.53  --prep_gs_sim                           true
% 8.19/1.53  --prep_unflatten                        true
% 8.19/1.53  --prep_res_sim                          true
% 8.19/1.53  --prep_upred                            true
% 8.19/1.53  --prep_sem_filter                       exhaustive
% 8.19/1.53  --prep_sem_filter_out                   false
% 8.19/1.53  --pred_elim                             true
% 8.19/1.53  --res_sim_input                         true
% 8.19/1.53  --eq_ax_congr_red                       true
% 8.19/1.53  --pure_diseq_elim                       true
% 8.19/1.53  --brand_transform                       false
% 8.19/1.53  --non_eq_to_eq                          false
% 8.19/1.53  --prep_def_merge                        true
% 8.19/1.53  --prep_def_merge_prop_impl              false
% 8.19/1.53  --prep_def_merge_mbd                    true
% 8.19/1.53  --prep_def_merge_tr_red                 false
% 8.19/1.53  --prep_def_merge_tr_cl                  false
% 8.19/1.53  --smt_preprocessing                     true
% 8.19/1.53  --smt_ac_axioms                         fast
% 8.19/1.53  --preprocessed_out                      false
% 8.19/1.53  --preprocessed_stats                    false
% 8.19/1.53  
% 8.19/1.53  ------ Abstraction refinement Options
% 8.19/1.53  
% 8.19/1.53  --abstr_ref                             []
% 8.19/1.53  --abstr_ref_prep                        false
% 8.19/1.53  --abstr_ref_until_sat                   false
% 8.19/1.53  --abstr_ref_sig_restrict                funpre
% 8.19/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 8.19/1.53  --abstr_ref_under                       []
% 8.19/1.53  
% 8.19/1.53  ------ SAT Options
% 8.19/1.53  
% 8.19/1.53  --sat_mode                              false
% 8.19/1.53  --sat_fm_restart_options                ""
% 8.19/1.53  --sat_gr_def                            false
% 8.19/1.53  --sat_epr_types                         true
% 8.19/1.53  --sat_non_cyclic_types                  false
% 8.19/1.53  --sat_finite_models                     false
% 8.19/1.53  --sat_fm_lemmas                         false
% 8.19/1.53  --sat_fm_prep                           false
% 8.19/1.53  --sat_fm_uc_incr                        true
% 8.19/1.53  --sat_out_model                         small
% 8.19/1.53  --sat_out_clauses                       false
% 8.19/1.53  
% 8.19/1.53  ------ QBF Options
% 8.19/1.53  
% 8.19/1.53  --qbf_mode                              false
% 8.19/1.53  --qbf_elim_univ                         false
% 8.19/1.53  --qbf_dom_inst                          none
% 8.19/1.53  --qbf_dom_pre_inst                      false
% 8.19/1.53  --qbf_sk_in                             false
% 8.19/1.53  --qbf_pred_elim                         true
% 8.19/1.53  --qbf_split                             512
% 8.19/1.53  
% 8.19/1.53  ------ BMC1 Options
% 8.19/1.53  
% 8.19/1.53  --bmc1_incremental                      false
% 8.19/1.53  --bmc1_axioms                           reachable_all
% 8.19/1.53  --bmc1_min_bound                        0
% 8.19/1.53  --bmc1_max_bound                        -1
% 8.19/1.53  --bmc1_max_bound_default                -1
% 8.19/1.53  --bmc1_symbol_reachability              true
% 8.19/1.53  --bmc1_property_lemmas                  false
% 8.19/1.53  --bmc1_k_induction                      false
% 8.19/1.53  --bmc1_non_equiv_states                 false
% 8.19/1.53  --bmc1_deadlock                         false
% 8.19/1.53  --bmc1_ucm                              false
% 8.19/1.53  --bmc1_add_unsat_core                   none
% 8.19/1.53  --bmc1_unsat_core_children              false
% 8.19/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 8.19/1.53  --bmc1_out_stat                         full
% 8.19/1.53  --bmc1_ground_init                      false
% 8.19/1.53  --bmc1_pre_inst_next_state              false
% 8.19/1.53  --bmc1_pre_inst_state                   false
% 8.19/1.53  --bmc1_pre_inst_reach_state             false
% 8.19/1.53  --bmc1_out_unsat_core                   false
% 8.19/1.53  --bmc1_aig_witness_out                  false
% 8.19/1.53  --bmc1_verbose                          false
% 8.19/1.53  --bmc1_dump_clauses_tptp                false
% 8.19/1.53  --bmc1_dump_unsat_core_tptp             false
% 8.19/1.53  --bmc1_dump_file                        -
% 8.19/1.53  --bmc1_ucm_expand_uc_limit              128
% 8.19/1.53  --bmc1_ucm_n_expand_iterations          6
% 8.19/1.53  --bmc1_ucm_extend_mode                  1
% 8.19/1.53  --bmc1_ucm_init_mode                    2
% 8.19/1.53  --bmc1_ucm_cone_mode                    none
% 8.19/1.53  --bmc1_ucm_reduced_relation_type        0
% 8.19/1.53  --bmc1_ucm_relax_model                  4
% 8.19/1.53  --bmc1_ucm_full_tr_after_sat            true
% 8.19/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 8.19/1.53  --bmc1_ucm_layered_model                none
% 8.19/1.53  --bmc1_ucm_max_lemma_size               10
% 8.19/1.53  
% 8.19/1.53  ------ AIG Options
% 8.19/1.53  
% 8.19/1.53  --aig_mode                              false
% 8.19/1.53  
% 8.19/1.53  ------ Instantiation Options
% 8.19/1.53  
% 8.19/1.53  --instantiation_flag                    true
% 8.19/1.53  --inst_sos_flag                         false
% 8.19/1.53  --inst_sos_phase                        true
% 8.19/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.19/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.19/1.53  --inst_lit_sel_side                     none
% 8.19/1.53  --inst_solver_per_active                1400
% 8.19/1.53  --inst_solver_calls_frac                1.
% 8.19/1.53  --inst_passive_queue_type               priority_queues
% 8.19/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.19/1.53  --inst_passive_queues_freq              [25;2]
% 8.19/1.53  --inst_dismatching                      true
% 8.19/1.53  --inst_eager_unprocessed_to_passive     true
% 8.19/1.53  --inst_prop_sim_given                   true
% 8.19/1.53  --inst_prop_sim_new                     false
% 8.19/1.53  --inst_subs_new                         false
% 8.19/1.53  --inst_eq_res_simp                      false
% 8.19/1.53  --inst_subs_given                       false
% 8.19/1.53  --inst_orphan_elimination               true
% 8.19/1.53  --inst_learning_loop_flag               true
% 8.19/1.53  --inst_learning_start                   3000
% 8.19/1.53  --inst_learning_factor                  2
% 8.19/1.53  --inst_start_prop_sim_after_learn       3
% 8.19/1.53  --inst_sel_renew                        solver
% 8.19/1.53  --inst_lit_activity_flag                true
% 8.19/1.53  --inst_restr_to_given                   false
% 8.19/1.53  --inst_activity_threshold               500
% 8.19/1.53  --inst_out_proof                        true
% 8.19/1.53  
% 8.19/1.53  ------ Resolution Options
% 8.19/1.53  
% 8.19/1.53  --resolution_flag                       false
% 8.19/1.53  --res_lit_sel                           adaptive
% 8.19/1.53  --res_lit_sel_side                      none
% 8.19/1.53  --res_ordering                          kbo
% 8.19/1.53  --res_to_prop_solver                    active
% 8.19/1.53  --res_prop_simpl_new                    false
% 8.19/1.53  --res_prop_simpl_given                  true
% 8.19/1.53  --res_passive_queue_type                priority_queues
% 8.19/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.19/1.53  --res_passive_queues_freq               [15;5]
% 8.19/1.53  --res_forward_subs                      full
% 8.19/1.53  --res_backward_subs                     full
% 8.19/1.53  --res_forward_subs_resolution           true
% 8.19/1.53  --res_backward_subs_resolution          true
% 8.19/1.53  --res_orphan_elimination                true
% 8.19/1.53  --res_time_limit                        2.
% 8.19/1.53  --res_out_proof                         true
% 8.19/1.53  
% 8.19/1.53  ------ Superposition Options
% 8.19/1.53  
% 8.19/1.53  --superposition_flag                    true
% 8.19/1.53  --sup_passive_queue_type                priority_queues
% 8.19/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.19/1.53  --sup_passive_queues_freq               [8;1;4]
% 8.19/1.53  --demod_completeness_check              fast
% 8.19/1.53  --demod_use_ground                      true
% 8.19/1.53  --sup_to_prop_solver                    passive
% 8.19/1.53  --sup_prop_simpl_new                    true
% 8.19/1.53  --sup_prop_simpl_given                  true
% 8.19/1.53  --sup_fun_splitting                     false
% 8.19/1.53  --sup_smt_interval                      50000
% 8.19/1.53  
% 8.19/1.53  ------ Superposition Simplification Setup
% 8.19/1.53  
% 8.19/1.53  --sup_indices_passive                   []
% 8.19/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.19/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.19/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.19/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 8.19/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.19/1.53  --sup_full_bw                           [BwDemod]
% 8.19/1.53  --sup_immed_triv                        [TrivRules]
% 8.19/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.19/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.19/1.53  --sup_immed_bw_main                     []
% 8.19/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.19/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 8.19/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.19/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.19/1.53  
% 8.19/1.53  ------ Combination Options
% 8.19/1.53  
% 8.19/1.53  --comb_res_mult                         3
% 8.19/1.53  --comb_sup_mult                         2
% 8.19/1.53  --comb_inst_mult                        10
% 8.19/1.53  
% 8.19/1.53  ------ Debug Options
% 8.19/1.53  
% 8.19/1.53  --dbg_backtrace                         false
% 8.19/1.53  --dbg_dump_prop_clauses                 false
% 8.19/1.53  --dbg_dump_prop_clauses_file            -
% 8.19/1.53  --dbg_out_stat                          false
% 8.19/1.53  
% 8.19/1.53  
% 8.19/1.53  
% 8.19/1.53  
% 8.19/1.53  ------ Proving...
% 8.19/1.53  
% 8.19/1.53  
% 8.19/1.53  % SZS status Theorem for theBenchmark.p
% 8.19/1.53  
% 8.19/1.53   Resolution empty clause
% 8.19/1.53  
% 8.19/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 8.19/1.53  
% 8.19/1.53  fof(f12,conjecture,(
% 8.19/1.53    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f13,negated_conjecture,(
% 8.19/1.53    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 8.19/1.53    inference(negated_conjecture,[],[f12])).
% 8.19/1.53  
% 8.19/1.53  fof(f15,plain,(
% 8.19/1.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 8.19/1.53    inference(ennf_transformation,[],[f13])).
% 8.19/1.53  
% 8.19/1.53  fof(f32,plain,(
% 8.19/1.53    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK4,sK5) = X0) )),
% 8.19/1.53    introduced(choice_axiom,[])).
% 8.19/1.53  
% 8.19/1.53  fof(f31,plain,(
% 8.19/1.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3) & ? [X2,X1] : k4_tarski(X1,X2) = sK3)),
% 8.19/1.53    introduced(choice_axiom,[])).
% 8.19/1.53  
% 8.19/1.53  fof(f33,plain,(
% 8.19/1.53    (k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3) & k4_tarski(sK4,sK5) = sK3),
% 8.19/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f32,f31])).
% 8.19/1.53  
% 8.19/1.53  fof(f61,plain,(
% 8.19/1.53    k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3),
% 8.19/1.53    inference(cnf_transformation,[],[f33])).
% 8.19/1.53  
% 8.19/1.53  fof(f60,plain,(
% 8.19/1.53    k4_tarski(sK4,sK5) = sK3),
% 8.19/1.53    inference(cnf_transformation,[],[f33])).
% 8.19/1.53  
% 8.19/1.53  fof(f10,axiom,(
% 8.19/1.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f55,plain,(
% 8.19/1.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 8.19/1.53    inference(cnf_transformation,[],[f10])).
% 8.19/1.53  
% 8.19/1.53  fof(f56,plain,(
% 8.19/1.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 8.19/1.53    inference(cnf_transformation,[],[f10])).
% 8.19/1.53  
% 8.19/1.53  fof(f9,axiom,(
% 8.19/1.53    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f54,plain,(
% 8.19/1.53    ( ! [X0,X1] : (k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))) )),
% 8.19/1.53    inference(cnf_transformation,[],[f9])).
% 8.19/1.53  
% 8.19/1.53  fof(f3,axiom,(
% 8.19/1.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f44,plain,(
% 8.19/1.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 8.19/1.53    inference(cnf_transformation,[],[f3])).
% 8.19/1.53  
% 8.19/1.53  fof(f4,axiom,(
% 8.19/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f45,plain,(
% 8.19/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 8.19/1.53    inference(cnf_transformation,[],[f4])).
% 8.19/1.53  
% 8.19/1.53  fof(f5,axiom,(
% 8.19/1.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f46,plain,(
% 8.19/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.19/1.53    inference(cnf_transformation,[],[f5])).
% 8.19/1.53  
% 8.19/1.53  fof(f62,plain,(
% 8.19/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 8.19/1.53    inference(definition_unfolding,[],[f45,f46])).
% 8.19/1.53  
% 8.19/1.53  fof(f63,plain,(
% 8.19/1.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 8.19/1.53    inference(definition_unfolding,[],[f44,f62])).
% 8.19/1.53  
% 8.19/1.53  fof(f74,plain,(
% 8.19/1.53    ( ! [X0,X1] : (k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 8.19/1.53    inference(definition_unfolding,[],[f54,f63,f63,f63])).
% 8.19/1.53  
% 8.19/1.53  fof(f2,axiom,(
% 8.19/1.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f20,plain,(
% 8.19/1.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 8.19/1.53    inference(nnf_transformation,[],[f2])).
% 8.19/1.53  
% 8.19/1.53  fof(f21,plain,(
% 8.19/1.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 8.19/1.53    inference(flattening,[],[f20])).
% 8.19/1.53  
% 8.19/1.53  fof(f22,plain,(
% 8.19/1.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 8.19/1.53    inference(rectify,[],[f21])).
% 8.19/1.53  
% 8.19/1.53  fof(f23,plain,(
% 8.19/1.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 8.19/1.53    introduced(choice_axiom,[])).
% 8.19/1.53  
% 8.19/1.53  fof(f24,plain,(
% 8.19/1.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 8.19/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 8.19/1.53  
% 8.19/1.53  fof(f39,plain,(
% 8.19/1.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 8.19/1.53    inference(cnf_transformation,[],[f24])).
% 8.19/1.53  
% 8.19/1.53  fof(f72,plain,(
% 8.19/1.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 8.19/1.53    inference(definition_unfolding,[],[f39,f62])).
% 8.19/1.53  
% 8.19/1.53  fof(f80,plain,(
% 8.19/1.53    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 8.19/1.53    inference(equality_resolution,[],[f72])).
% 8.19/1.53  
% 8.19/1.53  fof(f81,plain,(
% 8.19/1.53    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 8.19/1.53    inference(equality_resolution,[],[f80])).
% 8.19/1.53  
% 8.19/1.53  fof(f6,axiom,(
% 8.19/1.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f25,plain,(
% 8.19/1.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 8.19/1.53    inference(nnf_transformation,[],[f6])).
% 8.19/1.53  
% 8.19/1.53  fof(f26,plain,(
% 8.19/1.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 8.19/1.53    inference(flattening,[],[f25])).
% 8.19/1.53  
% 8.19/1.53  fof(f48,plain,(
% 8.19/1.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 8.19/1.53    inference(cnf_transformation,[],[f26])).
% 8.19/1.53  
% 8.19/1.53  fof(f11,axiom,(
% 8.19/1.53    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f14,plain,(
% 8.19/1.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 8.19/1.53    inference(ennf_transformation,[],[f11])).
% 8.19/1.53  
% 8.19/1.53  fof(f29,plain,(
% 8.19/1.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 8.19/1.53    introduced(choice_axiom,[])).
% 8.19/1.53  
% 8.19/1.53  fof(f30,plain,(
% 8.19/1.53    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 8.19/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f29])).
% 8.19/1.53  
% 8.19/1.53  fof(f57,plain,(
% 8.19/1.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 8.19/1.53    inference(cnf_transformation,[],[f30])).
% 8.19/1.53  
% 8.19/1.53  fof(f1,axiom,(
% 8.19/1.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f16,plain,(
% 8.19/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 8.19/1.53    inference(nnf_transformation,[],[f1])).
% 8.19/1.53  
% 8.19/1.53  fof(f17,plain,(
% 8.19/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 8.19/1.53    inference(rectify,[],[f16])).
% 8.19/1.53  
% 8.19/1.53  fof(f18,plain,(
% 8.19/1.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 8.19/1.53    introduced(choice_axiom,[])).
% 8.19/1.53  
% 8.19/1.53  fof(f19,plain,(
% 8.19/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 8.19/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 8.19/1.53  
% 8.19/1.53  fof(f34,plain,(
% 8.19/1.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 8.19/1.53    inference(cnf_transformation,[],[f19])).
% 8.19/1.53  
% 8.19/1.53  fof(f67,plain,(
% 8.19/1.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 8.19/1.53    inference(definition_unfolding,[],[f34,f63])).
% 8.19/1.53  
% 8.19/1.53  fof(f77,plain,(
% 8.19/1.53    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 8.19/1.53    inference(equality_resolution,[],[f67])).
% 8.19/1.53  
% 8.19/1.53  fof(f59,plain,(
% 8.19/1.53    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 8.19/1.53    inference(cnf_transformation,[],[f30])).
% 8.19/1.53  
% 8.19/1.53  fof(f7,axiom,(
% 8.19/1.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f27,plain,(
% 8.19/1.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 8.19/1.53    inference(nnf_transformation,[],[f7])).
% 8.19/1.53  
% 8.19/1.53  fof(f28,plain,(
% 8.19/1.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 8.19/1.53    inference(flattening,[],[f27])).
% 8.19/1.53  
% 8.19/1.53  fof(f52,plain,(
% 8.19/1.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 8.19/1.53    inference(cnf_transformation,[],[f28])).
% 8.19/1.53  
% 8.19/1.53  fof(f83,plain,(
% 8.19/1.53    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 8.19/1.53    inference(equality_resolution,[],[f52])).
% 8.19/1.53  
% 8.19/1.53  fof(f8,axiom,(
% 8.19/1.53    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 8.19/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.53  
% 8.19/1.53  fof(f53,plain,(
% 8.19/1.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 8.19/1.53    inference(cnf_transformation,[],[f8])).
% 8.19/1.53  
% 8.19/1.53  fof(f58,plain,(
% 8.19/1.53    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 8.19/1.53    inference(cnf_transformation,[],[f30])).
% 8.19/1.53  
% 8.19/1.53  fof(f35,plain,(
% 8.19/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 8.19/1.53    inference(cnf_transformation,[],[f19])).
% 8.19/1.53  
% 8.19/1.53  fof(f66,plain,(
% 8.19/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 8.19/1.53    inference(definition_unfolding,[],[f35,f63])).
% 8.19/1.53  
% 8.19/1.53  fof(f75,plain,(
% 8.19/1.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 8.19/1.53    inference(equality_resolution,[],[f66])).
% 8.19/1.53  
% 8.19/1.53  fof(f76,plain,(
% 8.19/1.53    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 8.19/1.53    inference(equality_resolution,[],[f75])).
% 8.19/1.53  
% 8.19/1.53  cnf(c_23,negated_conjecture,
% 8.19/1.53      ( k1_mcart_1(sK3) = sK3 | k2_mcart_1(sK3) = sK3 ),
% 8.19/1.53      inference(cnf_transformation,[],[f61]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_24,negated_conjecture,
% 8.19/1.53      ( k4_tarski(sK4,sK5) = sK3 ),
% 8.19/1.53      inference(cnf_transformation,[],[f60]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_19,plain,
% 8.19/1.53      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 8.19/1.53      inference(cnf_transformation,[],[f55]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_830,plain,
% 8.19/1.53      ( k1_mcart_1(sK3) = sK4 ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_24,c_19]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_832,plain,
% 8.19/1.53      ( k2_mcart_1(sK3) = sK3 | sK4 = sK3 ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_23,c_830]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_18,plain,
% 8.19/1.53      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 8.19/1.53      inference(cnf_transformation,[],[f56]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_644,plain,
% 8.19/1.53      ( k2_mcart_1(sK3) = sK5 ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_24,c_18]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_834,plain,
% 8.19/1.53      ( sK5 = sK3 | sK4 = sK3 ),
% 8.19/1.53      inference(demodulation,[status(thm)],[c_832,c_644]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_1475,plain,
% 8.19/1.53      ( k4_tarski(sK4,sK3) = sK3 | sK4 = sK3 ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_834,c_24]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_17,plain,
% 8.19/1.53      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
% 8.19/1.53      inference(cnf_transformation,[],[f74]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_8,plain,
% 8.19/1.53      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 8.19/1.53      inference(cnf_transformation,[],[f81]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_485,plain,
% 8.19/1.53      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 8.19/1.53      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_2375,plain,
% 8.19/1.53      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) = iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_17,c_485]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_4339,plain,
% 8.19/1.53      ( sK4 = sK3
% 8.19/1.53      | r2_hidden(sK3,k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_1475,c_2375]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_11,plain,
% 8.19/1.53      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 8.19/1.53      inference(cnf_transformation,[],[f48]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_482,plain,
% 8.19/1.53      ( r2_hidden(X0,X1) = iProver_top
% 8.19/1.53      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 8.19/1.53      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_3583,plain,
% 8.19/1.53      ( r2_hidden(sK5,X0) = iProver_top
% 8.19/1.53      | r2_hidden(sK3,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_24,c_482]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_5895,plain,
% 8.19/1.53      ( sK4 = sK3 | r2_hidden(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_4339,c_3583]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_22,plain,
% 8.19/1.53      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 8.19/1.53      inference(cnf_transformation,[],[f57]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_477,plain,
% 8.19/1.53      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 8.19/1.53      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_1034,plain,
% 8.19/1.53      ( k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_24,c_17]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_3,plain,
% 8.19/1.53      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 8.19/1.53      inference(cnf_transformation,[],[f77]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_490,plain,
% 8.19/1.53      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 8.19/1.53      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_2698,plain,
% 8.19/1.53      ( k4_tarski(X0,X1) = X2
% 8.19/1.53      | r2_hidden(X2,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_17,c_490]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_6542,plain,
% 8.19/1.53      ( k4_tarski(sK4,sK5) = X0
% 8.19/1.53      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_1034,c_2698]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_6562,plain,
% 8.19/1.53      ( sK3 = X0 | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 8.19/1.53      inference(demodulation,[status(thm)],[c_6542,c_24]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_6611,plain,
% 8.19/1.53      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 8.19/1.53      | sK2(k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_477,c_6562]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_20,plain,
% 8.19/1.53      ( ~ r2_hidden(X0,X1) | k4_tarski(X2,X0) != sK2(X1) | k1_xboole_0 = X1 ),
% 8.19/1.53      inference(cnf_transformation,[],[f59]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_479,plain,
% 8.19/1.53      ( k4_tarski(X0,X1) != sK2(X2)
% 8.19/1.53      | k1_xboole_0 = X2
% 8.19/1.53      | r2_hidden(X1,X2) != iProver_top ),
% 8.19/1.53      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_2355,plain,
% 8.19/1.53      ( sK2(X0) != sK3 | k1_xboole_0 = X0 | r2_hidden(sK5,X0) != iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_24,c_479]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_7810,plain,
% 8.19/1.53      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 8.19/1.53      | r2_hidden(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_6611,c_2355]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_7853,plain,
% 8.19/1.53      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 | sK4 = sK3 ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_5895,c_7810]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_27403,plain,
% 8.19/1.53      ( sK4 = sK3 | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_7853,c_5895]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_13,plain,
% 8.19/1.53      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 8.19/1.53      inference(cnf_transformation,[],[f83]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_16,plain,
% 8.19/1.53      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 8.19/1.53      inference(cnf_transformation,[],[f53]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_480,plain,
% 8.19/1.53      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 8.19/1.53      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_1040,plain,
% 8.19/1.53      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_13,c_480]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_28081,plain,
% 8.19/1.53      ( sK4 = sK3 ),
% 8.19/1.53      inference(forward_subsumption_resolution,[status(thm)],[c_27403,c_1040]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_21,plain,
% 8.19/1.53      ( ~ r2_hidden(X0,X1) | k4_tarski(X0,X2) != sK2(X1) | k1_xboole_0 = X1 ),
% 8.19/1.53      inference(cnf_transformation,[],[f58]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_478,plain,
% 8.19/1.53      ( k4_tarski(X0,X1) != sK2(X2)
% 8.19/1.53      | k1_xboole_0 = X2
% 8.19/1.53      | r2_hidden(X0,X2) != iProver_top ),
% 8.19/1.53      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_913,plain,
% 8.19/1.53      ( sK2(X0) != sK3 | k1_xboole_0 = X0 | r2_hidden(sK4,X0) != iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_24,c_478]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_7812,plain,
% 8.19/1.53      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 8.19/1.53      | r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_6611,c_913]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_28101,plain,
% 8.19/1.53      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 8.19/1.53      | r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 8.19/1.53      inference(demodulation,[status(thm)],[c_28081,c_7812]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_2,plain,
% 8.19/1.53      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 8.19/1.53      inference(cnf_transformation,[],[f76]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_10045,plain,
% 8.19/1.53      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 8.19/1.53      inference(instantiation,[status(thm)],[c_2]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_10046,plain,
% 8.19/1.53      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 8.19/1.53      inference(predicate_to_equality,[status(thm)],[c_10045]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_32278,plain,
% 8.19/1.53      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 8.19/1.53      inference(global_propositional_subsumption,
% 8.19/1.53                [status(thm)],
% 8.19/1.53                [c_28101,c_10046]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_32365,plain,
% 8.19/1.53      ( r2_hidden(k4_tarski(X0,sK3),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k1_xboole_0)) = iProver_top ),
% 8.19/1.53      inference(superposition,[status(thm)],[c_32278,c_2375]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_32409,plain,
% 8.19/1.53      ( r2_hidden(k4_tarski(X0,sK3),k1_xboole_0) = iProver_top ),
% 8.19/1.53      inference(demodulation,[status(thm)],[c_32365,c_13]) ).
% 8.19/1.53  
% 8.19/1.53  cnf(c_32942,plain,
% 8.19/1.53      ( $false ),
% 8.19/1.53      inference(forward_subsumption_resolution,[status(thm)],[c_32409,c_1040]) ).
% 8.19/1.53  
% 8.19/1.53  
% 8.19/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 8.19/1.53  
% 8.19/1.53  ------                               Statistics
% 8.19/1.53  
% 8.19/1.53  ------ General
% 8.19/1.53  
% 8.19/1.53  abstr_ref_over_cycles:                  0
% 8.19/1.53  abstr_ref_under_cycles:                 0
% 8.19/1.53  gc_basic_clause_elim:                   0
% 8.19/1.53  forced_gc_time:                         0
% 8.19/1.53  parsing_time:                           0.01
% 8.19/1.53  unif_index_cands_time:                  0.
% 8.19/1.53  unif_index_add_time:                    0.
% 8.19/1.53  orderings_time:                         0.
% 8.19/1.53  out_proof_time:                         0.011
% 8.19/1.53  total_time:                             1.022
% 8.19/1.53  num_of_symbols:                         44
% 8.19/1.53  num_of_terms:                           36955
% 8.19/1.53  
% 8.19/1.53  ------ Preprocessing
% 8.19/1.53  
% 8.19/1.53  num_of_splits:                          0
% 8.19/1.53  num_of_split_atoms:                     0
% 8.19/1.53  num_of_reused_defs:                     0
% 8.19/1.53  num_eq_ax_congr_red:                    12
% 8.19/1.53  num_of_sem_filtered_clauses:            1
% 8.19/1.53  num_of_subtypes:                        0
% 8.19/1.53  monotx_restored_types:                  0
% 8.19/1.53  sat_num_of_epr_types:                   0
% 8.19/1.53  sat_num_of_non_cyclic_types:            0
% 8.19/1.53  sat_guarded_non_collapsed_types:        0
% 8.19/1.53  num_pure_diseq_elim:                    0
% 8.19/1.53  simp_replaced_by:                       0
% 8.19/1.53  res_preprocessed:                       92
% 8.19/1.53  prep_upred:                             0
% 8.19/1.53  prep_unflattend:                        0
% 8.19/1.53  smt_new_axioms:                         0
% 8.19/1.53  pred_elim_cands:                        1
% 8.19/1.53  pred_elim:                              0
% 8.19/1.53  pred_elim_cl:                           0
% 8.19/1.53  pred_elim_cycles:                       1
% 8.19/1.53  merged_defs:                            0
% 8.19/1.53  merged_defs_ncl:                        0
% 8.19/1.53  bin_hyper_res:                          0
% 8.19/1.53  prep_cycles:                            3
% 8.19/1.53  pred_elim_time:                         0.
% 8.19/1.53  splitting_time:                         0.
% 8.19/1.53  sem_filter_time:                        0.
% 8.19/1.53  monotx_time:                            0.
% 8.19/1.53  subtype_inf_time:                       0.
% 8.19/1.53  
% 8.19/1.53  ------ Problem properties
% 8.19/1.53  
% 8.19/1.53  clauses:                                25
% 8.19/1.53  conjectures:                            2
% 8.19/1.53  epr:                                    0
% 8.19/1.53  horn:                                   19
% 8.19/1.53  ground:                                 2
% 8.19/1.53  unary:                                  10
% 8.19/1.53  binary:                                 5
% 8.19/1.53  lits:                                   51
% 8.19/1.53  lits_eq:                                30
% 8.19/1.53  fd_pure:                                0
% 8.19/1.53  fd_pseudo:                              0
% 8.19/1.53  fd_cond:                                4
% 8.19/1.53  fd_pseudo_cond:                         5
% 8.19/1.53  ac_symbols:                             0
% 8.19/1.53  
% 8.19/1.53  ------ Propositional Solver
% 8.19/1.53  
% 8.19/1.53  prop_solver_calls:                      27
% 8.19/1.53  prop_fast_solver_calls:                 725
% 8.19/1.53  smt_solver_calls:                       0
% 8.19/1.53  smt_fast_solver_calls:                  0
% 8.19/1.53  prop_num_of_clauses:                    9830
% 8.19/1.53  prop_preprocess_simplified:             30156
% 8.19/1.53  prop_fo_subsumed:                       5
% 8.19/1.53  prop_solver_time:                       0.
% 8.19/1.53  smt_solver_time:                        0.
% 8.19/1.53  smt_fast_solver_time:                   0.
% 8.19/1.53  prop_fast_solver_time:                  0.
% 8.19/1.53  prop_unsat_core_time:                   0.
% 8.19/1.53  
% 8.19/1.53  ------ QBF
% 8.19/1.53  
% 8.19/1.53  qbf_q_res:                              0
% 8.19/1.53  qbf_num_tautologies:                    0
% 8.19/1.53  qbf_prep_cycles:                        0
% 8.19/1.53  
% 8.19/1.53  ------ BMC1
% 8.19/1.53  
% 8.19/1.53  bmc1_current_bound:                     -1
% 8.19/1.53  bmc1_last_solved_bound:                 -1
% 8.19/1.53  bmc1_unsat_core_size:                   -1
% 8.19/1.53  bmc1_unsat_core_parents_size:           -1
% 8.19/1.53  bmc1_merge_next_fun:                    0
% 8.19/1.53  bmc1_unsat_core_clauses_time:           0.
% 8.19/1.53  
% 8.19/1.53  ------ Instantiation
% 8.19/1.53  
% 8.19/1.53  inst_num_of_clauses:                    3212
% 8.19/1.53  inst_num_in_passive:                    2151
% 8.19/1.53  inst_num_in_active:                     637
% 8.19/1.53  inst_num_in_unprocessed:                425
% 8.19/1.53  inst_num_of_loops:                      660
% 8.19/1.53  inst_num_of_learning_restarts:          0
% 8.19/1.53  inst_num_moves_active_passive:          22
% 8.19/1.53  inst_lit_activity:                      0
% 8.19/1.53  inst_lit_activity_moves:                0
% 8.19/1.53  inst_num_tautologies:                   0
% 8.19/1.53  inst_num_prop_implied:                  0
% 8.19/1.53  inst_num_existing_simplified:           0
% 8.19/1.53  inst_num_eq_res_simplified:             0
% 8.19/1.53  inst_num_child_elim:                    0
% 8.19/1.53  inst_num_of_dismatching_blockings:      2142
% 8.19/1.53  inst_num_of_non_proper_insts:           5354
% 8.19/1.53  inst_num_of_duplicates:                 0
% 8.19/1.53  inst_inst_num_from_inst_to_res:         0
% 8.19/1.53  inst_dismatching_checking_time:         0.
% 8.19/1.53  
% 8.19/1.53  ------ Resolution
% 8.19/1.53  
% 8.19/1.53  res_num_of_clauses:                     0
% 8.19/1.53  res_num_in_passive:                     0
% 8.19/1.53  res_num_in_active:                      0
% 8.19/1.53  res_num_of_loops:                       95
% 8.19/1.53  res_forward_subset_subsumed:            1094
% 8.19/1.53  res_backward_subset_subsumed:           2
% 8.19/1.53  res_forward_subsumed:                   0
% 8.19/1.53  res_backward_subsumed:                  0
% 8.19/1.53  res_forward_subsumption_resolution:     0
% 8.19/1.53  res_backward_subsumption_resolution:    0
% 8.19/1.53  res_clause_to_clause_subsumption:       5014
% 8.19/1.53  res_orphan_elimination:                 0
% 8.19/1.53  res_tautology_del:                      54
% 8.19/1.53  res_num_eq_res_simplified:              0
% 8.19/1.53  res_num_sel_changes:                    0
% 8.19/1.53  res_moves_from_active_to_pass:          0
% 8.19/1.53  
% 8.19/1.53  ------ Superposition
% 8.19/1.53  
% 8.19/1.53  sup_time_total:                         0.
% 8.19/1.53  sup_time_generating:                    0.
% 8.19/1.53  sup_time_sim_full:                      0.
% 8.19/1.53  sup_time_sim_immed:                     0.
% 8.19/1.53  
% 8.19/1.53  sup_num_of_clauses:                     661
% 8.19/1.53  sup_num_in_active:                      54
% 8.19/1.53  sup_num_in_passive:                     607
% 8.19/1.53  sup_num_of_loops:                       131
% 8.19/1.53  sup_fw_superposition:                   783
% 8.19/1.53  sup_bw_superposition:                   630
% 8.19/1.53  sup_immediate_simplified:               408
% 8.19/1.53  sup_given_eliminated:                   2
% 8.19/1.53  comparisons_done:                       0
% 8.19/1.53  comparisons_avoided:                    36
% 8.19/1.53  
% 8.19/1.53  ------ Simplifications
% 8.19/1.53  
% 8.19/1.53  
% 8.19/1.53  sim_fw_subset_subsumed:                 70
% 8.19/1.53  sim_bw_subset_subsumed:                 143
% 8.19/1.53  sim_fw_subsumed:                        226
% 8.19/1.53  sim_bw_subsumed:                        13
% 8.19/1.53  sim_fw_subsumption_res:                 4
% 8.19/1.53  sim_bw_subsumption_res:                 0
% 8.19/1.53  sim_tautology_del:                      30
% 8.19/1.53  sim_eq_tautology_del:                   19
% 8.19/1.53  sim_eq_res_simp:                        0
% 8.19/1.53  sim_fw_demodulated:                     174
% 8.19/1.53  sim_bw_demodulated:                     43
% 8.19/1.53  sim_light_normalised:                   76
% 8.19/1.53  sim_joinable_taut:                      0
% 8.19/1.53  sim_joinable_simp:                      0
% 8.19/1.53  sim_ac_normalised:                      0
% 8.19/1.53  sim_smt_subsumption:                    0
% 8.19/1.53  
%------------------------------------------------------------------------------
