%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:34 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 229 expanded)
%              Number of clauses        :   39 (  54 expanded)
%              Number of leaves         :   14 (  52 expanded)
%              Depth                    :   20
%              Number of atoms          :  343 ( 810 expanded)
%              Number of equality atoms :  125 ( 287 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f53,f61])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f55,f61])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
       => ( r2_hidden(k2_mcart_1(X0),X3)
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK3),sK6)
        | ( k1_mcart_1(sK3) != sK5
          & k1_mcart_1(sK3) != sK4 ) )
      & r2_hidden(sK3,k2_zfmisc_1(k2_tarski(sK4,sK5),sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK3),sK6)
      | ( k1_mcart_1(sK3) != sK5
        & k1_mcart_1(sK3) != sK4 ) )
    & r2_hidden(sK3,k2_zfmisc_1(k2_tarski(sK4,sK5),sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f14,f32])).

fof(f58,plain,(
    r2_hidden(sK3,k2_zfmisc_1(k2_tarski(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    r2_hidden(sK3,k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f62])).

fof(f78,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f59,plain,
    ( ~ r2_hidden(k2_mcart_1(sK3),sK6)
    | k1_mcart_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,
    ( ~ r2_hidden(k2_mcart_1(sK3),sK6)
    | k1_mcart_1(sK3) != sK5 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7202,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_7197,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7406,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7202,c_7197])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_7198,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7411,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7202,c_7198])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_7206,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7199,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK3,k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7194,plain,
    ( r2_hidden(sK3,k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7195,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7355,plain,
    ( r2_hidden(k1_mcart_1(sK3),k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7194,c_7195])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7207,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7488,plain,
    ( r2_hidden(k1_mcart_1(sK3),X0) = iProver_top
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7355,c_7207])).

cnf(c_7705,plain,
    ( r2_hidden(k1_mcart_1(sK3),X0) = iProver_top
    | r2_hidden(sK4,X0) != iProver_top
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7199,c_7488])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7205,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7818,plain,
    ( r2_hidden(k1_mcart_1(sK3),X0) != iProver_top
    | r2_hidden(sK4,k4_xboole_0(X1,X0)) != iProver_top
    | r2_hidden(sK5,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7705,c_7205])).

cnf(c_7883,plain,
    ( r2_hidden(k1_mcart_1(sK3),X0) != iProver_top
    | r2_hidden(sK4,X1) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK5,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7206,c_7818])).

cnf(c_7897,plain,
    ( r2_hidden(k1_mcart_1(sK3),X0) != iProver_top
    | r2_hidden(sK4,X1) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK5,X1) != iProver_top
    | r2_hidden(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7206,c_7883])).

cnf(c_7909,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r2_hidden(sK4,k2_enumset1(X1,X1,X1,k1_mcart_1(sK3))) = iProver_top
    | r2_hidden(sK5,X0) != iProver_top
    | r2_hidden(sK5,k2_enumset1(X1,X1,X1,k1_mcart_1(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7411,c_7897])).

cnf(c_8117,plain,
    ( r2_hidden(sK4,k2_enumset1(X0,X0,X0,k1_mcart_1(sK3))) = iProver_top
    | r2_hidden(sK5,k2_enumset1(X0,X0,X0,k1_mcart_1(sK3))) = iProver_top
    | r2_hidden(sK5,k2_enumset1(X1,X1,X1,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7411,c_7909])).

cnf(c_8817,plain,
    ( r2_hidden(sK4,k2_enumset1(X0,X0,X0,k1_mcart_1(sK3))) = iProver_top
    | r2_hidden(sK5,k2_enumset1(X0,X0,X0,k1_mcart_1(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7406,c_8117])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_7200,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8908,plain,
    ( k1_mcart_1(sK3) = sK4
    | r2_hidden(sK5,k2_enumset1(k1_mcart_1(sK3),k1_mcart_1(sK3),k1_mcart_1(sK3),k1_mcart_1(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8817,c_7200])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(sK3),sK6)
    | k1_mcart_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2023,plain,
    ( r2_hidden(k2_mcart_1(sK3),sK6)
    | ~ r2_hidden(sK3,k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_8965,plain,
    ( r2_hidden(sK5,k2_enumset1(k1_mcart_1(sK3),k1_mcart_1(sK3),k1_mcart_1(sK3),k1_mcart_1(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8908,c_23,c_22,c_2023])).

cnf(c_8972,plain,
    ( k1_mcart_1(sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_8965,c_7200])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(sK3),sK6)
    | k1_mcart_1(sK3) != sK5 ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8972,c_2023,c_21,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:52:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.47/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/0.99  
% 3.47/0.99  ------  iProver source info
% 3.47/0.99  
% 3.47/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.47/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/0.99  git: non_committed_changes: false
% 3.47/0.99  git: last_make_outside_of_git: false
% 3.47/0.99  
% 3.47/0.99  ------ 
% 3.47/0.99  ------ Parsing...
% 3.47/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  ------ Proving...
% 3.47/0.99  ------ Problem Properties 
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  clauses                                 23
% 3.47/0.99  conjectures                             4
% 3.47/0.99  EPR                                     3
% 3.47/0.99  Horn                                    17
% 3.47/0.99  unary                                   3
% 3.47/0.99  binary                                  11
% 3.47/0.99  lits                                    53
% 3.47/0.99  lits eq                                 11
% 3.47/0.99  fd_pure                                 0
% 3.47/0.99  fd_pseudo                               0
% 3.47/0.99  fd_cond                                 0
% 3.47/0.99  fd_pseudo_cond                          6
% 3.47/0.99  AC symbols                              0
% 3.47/0.99  
% 3.47/0.99  ------ Input Options Time Limit: Unbounded
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing...
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.47/0.99  Current options:
% 3.47/0.99  ------ 
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing...
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing...
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing...
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS status Theorem for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  fof(f3,axiom,(
% 3.47/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f24,plain,(
% 3.47/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.47/0.99    inference(nnf_transformation,[],[f3])).
% 3.47/0.99  
% 3.47/0.99  fof(f25,plain,(
% 3.47/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.47/0.99    inference(flattening,[],[f24])).
% 3.47/0.99  
% 3.47/0.99  fof(f43,plain,(
% 3.47/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.47/0.99    inference(cnf_transformation,[],[f25])).
% 3.47/0.99  
% 3.47/0.99  fof(f75,plain,(
% 3.47/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.47/0.99    inference(equality_resolution,[],[f43])).
% 3.47/0.99  
% 3.47/0.99  fof(f8,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f30,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.47/0.99    inference(nnf_transformation,[],[f8])).
% 3.47/0.99  
% 3.47/0.99  fof(f31,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.47/0.99    inference(flattening,[],[f30])).
% 3.47/0.99  
% 3.47/0.99  fof(f53,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f31])).
% 3.47/0.99  
% 3.47/0.99  fof(f6,axiom,(
% 3.47/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f51,plain,(
% 3.47/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f6])).
% 3.47/0.99  
% 3.47/0.99  fof(f7,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f52,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f7])).
% 3.47/0.99  
% 3.47/0.99  fof(f61,plain,(
% 3.47/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.47/0.99    inference(definition_unfolding,[],[f51,f52])).
% 3.47/0.99  
% 3.47/0.99  fof(f69,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 3.47/0.99    inference(definition_unfolding,[],[f53,f61])).
% 3.47/0.99  
% 3.47/0.99  fof(f54,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f31])).
% 3.47/0.99  
% 3.47/0.99  fof(f68,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 3.47/0.99    inference(definition_unfolding,[],[f54,f61])).
% 3.47/0.99  
% 3.47/0.99  fof(f2,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f19,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.47/0.99    inference(nnf_transformation,[],[f2])).
% 3.47/0.99  
% 3.47/0.99  fof(f20,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.47/0.99    inference(flattening,[],[f19])).
% 3.47/0.99  
% 3.47/0.99  fof(f21,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.47/0.99    inference(rectify,[],[f20])).
% 3.47/0.99  
% 3.47/0.99  fof(f22,plain,(
% 3.47/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f23,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 3.47/0.99  
% 3.47/0.99  fof(f39,plain,(
% 3.47/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.47/0.99    inference(cnf_transformation,[],[f23])).
% 3.47/0.99  
% 3.47/0.99  fof(f71,plain,(
% 3.47/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.47/0.99    inference(equality_resolution,[],[f39])).
% 3.47/0.99  
% 3.47/0.99  fof(f55,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f31])).
% 3.47/0.99  
% 3.47/0.99  fof(f67,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.47/0.99    inference(definition_unfolding,[],[f55,f61])).
% 3.47/0.99  
% 3.47/0.99  fof(f10,conjecture,(
% 3.47/0.99    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f11,negated_conjecture,(
% 3.47/0.99    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 3.47/0.99    inference(negated_conjecture,[],[f10])).
% 3.47/0.99  
% 3.47/0.99  fof(f14,plain,(
% 3.47/0.99    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 3.47/0.99    inference(ennf_transformation,[],[f11])).
% 3.47/0.99  
% 3.47/0.99  fof(f32,plain,(
% 3.47/0.99    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) => ((~r2_hidden(k2_mcart_1(sK3),sK6) | (k1_mcart_1(sK3) != sK5 & k1_mcart_1(sK3) != sK4)) & r2_hidden(sK3,k2_zfmisc_1(k2_tarski(sK4,sK5),sK6)))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f33,plain,(
% 3.47/0.99    (~r2_hidden(k2_mcart_1(sK3),sK6) | (k1_mcart_1(sK3) != sK5 & k1_mcart_1(sK3) != sK4)) & r2_hidden(sK3,k2_zfmisc_1(k2_tarski(sK4,sK5),sK6))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f14,f32])).
% 3.47/0.99  
% 3.47/0.99  fof(f58,plain,(
% 3.47/0.99    r2_hidden(sK3,k2_zfmisc_1(k2_tarski(sK4,sK5),sK6))),
% 3.47/0.99    inference(cnf_transformation,[],[f33])).
% 3.47/0.99  
% 3.47/0.99  fof(f70,plain,(
% 3.47/0.99    r2_hidden(sK3,k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK5),sK6))),
% 3.47/0.99    inference(definition_unfolding,[],[f58,f61])).
% 3.47/0.99  
% 3.47/0.99  fof(f9,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f13,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.47/0.99    inference(ennf_transformation,[],[f9])).
% 3.47/0.99  
% 3.47/0.99  fof(f56,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f13])).
% 3.47/0.99  
% 3.47/0.99  fof(f1,axiom,(
% 3.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f12,plain,(
% 3.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f1])).
% 3.47/0.99  
% 3.47/0.99  fof(f15,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(nnf_transformation,[],[f12])).
% 3.47/0.99  
% 3.47/0.99  fof(f16,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(rectify,[],[f15])).
% 3.47/0.99  
% 3.47/0.99  fof(f17,plain,(
% 3.47/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f18,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 3.47/0.99  
% 3.47/0.99  fof(f34,plain,(
% 3.47/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f18])).
% 3.47/0.99  
% 3.47/0.99  fof(f38,plain,(
% 3.47/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.47/0.99    inference(cnf_transformation,[],[f23])).
% 3.47/0.99  
% 3.47/0.99  fof(f72,plain,(
% 3.47/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.47/0.99    inference(equality_resolution,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f4,axiom,(
% 3.47/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f26,plain,(
% 3.47/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.47/0.99    inference(nnf_transformation,[],[f4])).
% 3.47/0.99  
% 3.47/0.99  fof(f27,plain,(
% 3.47/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.47/0.99    inference(rectify,[],[f26])).
% 3.47/0.99  
% 3.47/0.99  fof(f28,plain,(
% 3.47/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f29,plain,(
% 3.47/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 3.47/0.99  
% 3.47/0.99  fof(f46,plain,(
% 3.47/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.47/0.99    inference(cnf_transformation,[],[f29])).
% 3.47/0.99  
% 3.47/0.99  fof(f5,axiom,(
% 3.47/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f50,plain,(
% 3.47/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f5])).
% 3.47/0.99  
% 3.47/0.99  fof(f62,plain,(
% 3.47/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.47/0.99    inference(definition_unfolding,[],[f50,f61])).
% 3.47/0.99  
% 3.47/0.99  fof(f66,plain,(
% 3.47/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.47/0.99    inference(definition_unfolding,[],[f46,f62])).
% 3.47/0.99  
% 3.47/0.99  fof(f78,plain,(
% 3.47/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.47/0.99    inference(equality_resolution,[],[f66])).
% 3.47/0.99  
% 3.47/0.99  fof(f59,plain,(
% 3.47/0.99    ~r2_hidden(k2_mcart_1(sK3),sK6) | k1_mcart_1(sK3) != sK4),
% 3.47/0.99    inference(cnf_transformation,[],[f33])).
% 3.47/0.99  
% 3.47/0.99  fof(f57,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f13])).
% 3.47/0.99  
% 3.47/0.99  fof(f60,plain,(
% 3.47/0.99    ~r2_hidden(k2_mcart_1(sK3),sK6) | k1_mcart_1(sK3) != sK5),
% 3.47/0.99    inference(cnf_transformation,[],[f33])).
% 3.47/0.99  
% 3.47/0.99  cnf(c_11,plain,
% 3.47/0.99      ( r1_tarski(X0,X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7202,plain,
% 3.47/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_18,plain,
% 3.47/0.99      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7197,plain,
% 3.47/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.47/0.99      | r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7406,plain,
% 3.47/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7202,c_7197]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_17,plain,
% 3.47/0.99      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7198,plain,
% 3.47/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.47/0.99      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7411,plain,
% 3.47/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7202,c_7198]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,X1)
% 3.47/0.99      | r2_hidden(X0,X2)
% 3.47/0.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7206,plain,
% 3.47/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.47/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.47/0.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_16,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,X1)
% 3.47/0.99      | ~ r2_hidden(X2,X1)
% 3.47/0.99      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7199,plain,
% 3.47/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.47/0.99      | r2_hidden(X2,X1) != iProver_top
% 3.47/0.99      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_23,negated_conjecture,
% 3.47/0.99      ( r2_hidden(sK3,k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK5),sK6)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7194,plain,
% 3.47/0.99      ( r2_hidden(sK3,k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK5),sK6)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_20,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.47/0.99      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7195,plain,
% 3.47/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.47/0.99      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7355,plain,
% 3.47/0.99      ( r2_hidden(k1_mcart_1(sK3),k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7194,c_7195]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.47/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7207,plain,
% 3.47/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.47/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.47/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7488,plain,
% 3.47/0.99      ( r2_hidden(k1_mcart_1(sK3),X0) = iProver_top
% 3.47/0.99      | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),X0) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7355,c_7207]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7705,plain,
% 3.47/0.99      ( r2_hidden(k1_mcart_1(sK3),X0) = iProver_top
% 3.47/0.99      | r2_hidden(sK4,X0) != iProver_top
% 3.47/0.99      | r2_hidden(sK5,X0) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7199,c_7488]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7,negated_conjecture,
% 3.47/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7205,plain,
% 3.47/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.47/0.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7818,plain,
% 3.47/0.99      ( r2_hidden(k1_mcart_1(sK3),X0) != iProver_top
% 3.47/0.99      | r2_hidden(sK4,k4_xboole_0(X1,X0)) != iProver_top
% 3.47/0.99      | r2_hidden(sK5,k4_xboole_0(X1,X0)) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7705,c_7205]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7883,plain,
% 3.47/0.99      ( r2_hidden(k1_mcart_1(sK3),X0) != iProver_top
% 3.47/0.99      | r2_hidden(sK4,X1) != iProver_top
% 3.47/0.99      | r2_hidden(sK4,X0) = iProver_top
% 3.47/0.99      | r2_hidden(sK5,k4_xboole_0(X1,X0)) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7206,c_7818]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7897,plain,
% 3.47/0.99      ( r2_hidden(k1_mcart_1(sK3),X0) != iProver_top
% 3.47/0.99      | r2_hidden(sK4,X1) != iProver_top
% 3.47/0.99      | r2_hidden(sK4,X0) = iProver_top
% 3.47/0.99      | r2_hidden(sK5,X1) != iProver_top
% 3.47/0.99      | r2_hidden(sK5,X0) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7206,c_7883]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7909,plain,
% 3.47/0.99      ( r2_hidden(sK4,X0) != iProver_top
% 3.47/0.99      | r2_hidden(sK4,k2_enumset1(X1,X1,X1,k1_mcart_1(sK3))) = iProver_top
% 3.47/0.99      | r2_hidden(sK5,X0) != iProver_top
% 3.47/0.99      | r2_hidden(sK5,k2_enumset1(X1,X1,X1,k1_mcart_1(sK3))) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7411,c_7897]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_8117,plain,
% 3.47/0.99      ( r2_hidden(sK4,k2_enumset1(X0,X0,X0,k1_mcart_1(sK3))) = iProver_top
% 3.47/0.99      | r2_hidden(sK5,k2_enumset1(X0,X0,X0,k1_mcart_1(sK3))) = iProver_top
% 3.47/0.99      | r2_hidden(sK5,k2_enumset1(X1,X1,X1,sK4)) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7411,c_7909]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_8817,plain,
% 3.47/0.99      ( r2_hidden(sK4,k2_enumset1(X0,X0,X0,k1_mcart_1(sK3))) = iProver_top
% 3.47/0.99      | r2_hidden(sK5,k2_enumset1(X0,X0,X0,k1_mcart_1(sK3))) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7406,c_8117]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_15,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.47/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7200,plain,
% 3.47/0.99      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_8908,plain,
% 3.47/0.99      ( k1_mcart_1(sK3) = sK4
% 3.47/0.99      | r2_hidden(sK5,k2_enumset1(k1_mcart_1(sK3),k1_mcart_1(sK3),k1_mcart_1(sK3),k1_mcart_1(sK3))) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_8817,c_7200]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_22,negated_conjecture,
% 3.47/0.99      ( ~ r2_hidden(k2_mcart_1(sK3),sK6) | k1_mcart_1(sK3) != sK4 ),
% 3.47/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_19,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.47/0.99      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.47/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2023,plain,
% 3.47/0.99      ( r2_hidden(k2_mcart_1(sK3),sK6)
% 3.47/0.99      | ~ r2_hidden(sK3,k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK5),sK6)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_8965,plain,
% 3.47/0.99      ( r2_hidden(sK5,k2_enumset1(k1_mcart_1(sK3),k1_mcart_1(sK3),k1_mcart_1(sK3),k1_mcart_1(sK3))) = iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_8908,c_23,c_22,c_2023]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_8972,plain,
% 3.47/0.99      ( k1_mcart_1(sK3) = sK5 ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_8965,c_7200]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_21,negated_conjecture,
% 3.47/0.99      ( ~ r2_hidden(k2_mcart_1(sK3),sK6) | k1_mcart_1(sK3) != sK5 ),
% 3.47/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(contradiction,plain,
% 3.47/0.99      ( $false ),
% 3.47/0.99      inference(minisat,[status(thm)],[c_8972,c_2023,c_21,c_23]) ).
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  ------                               Statistics
% 3.47/0.99  
% 3.47/0.99  ------ Selected
% 3.47/0.99  
% 3.47/0.99  total_time:                             0.25
% 3.47/0.99  
%------------------------------------------------------------------------------
