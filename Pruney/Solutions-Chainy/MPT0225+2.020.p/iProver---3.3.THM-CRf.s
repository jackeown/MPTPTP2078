%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:07 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  114 (1177 expanded)
%              Number of clauses        :   55 ( 160 expanded)
%              Number of leaves         :   19 ( 366 expanded)
%              Depth                    :   19
%              Number of atoms          :  323 (2217 expanded)
%              Number of equality atoms :  121 (1496 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
        & ( X0 != X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) )
   => ( ( sK2 = sK3
        | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2) )
      & ( sK2 != sK3
        | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( sK2 = sK3
      | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2) )
    & ( sK2 != sK3
      | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f29])).

fof(f50,plain,
    ( sK2 != sK3
    | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f53])).

fof(f60,plain,
    ( sK2 != sK3
    | k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f50,f37,f54,f54,f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f49,f54,f54])).

fof(f65,plain,(
    ! [X1] : ~ r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f58])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f51,plain,
    ( sK2 = sK3
    | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,
    ( sK2 = sK3
    | k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f51,f37,f54,f54,f54])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

cnf(c_621,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_618,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2711,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_621,c_618])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5486,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(resolution,[status(thm)],[c_2711,c_3])).

cnf(c_625,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | k3_enumset1(X0,X2,X4,X6,X8) = k3_enumset1(X1,X3,X5,X7,X9) ),
    theory(equality)).

cnf(c_620,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3882,plain,
    ( ~ r1_xboole_0(X0,k3_enumset1(X1,X2,X3,X4,X5))
    | r1_xboole_0(X6,k3_enumset1(X7,X8,X9,X10,X11))
    | X6 != X0
    | X7 != X1
    | X8 != X2
    | X9 != X3
    | X10 != X4
    | X11 != X5 ),
    inference(resolution,[status(thm)],[c_625,c_620])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1216,plain,
    ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK2 != sK3 ),
    inference(resolution,[status(thm)],[c_6,c_15])).

cnf(c_18605,plain,
    ( r1_xboole_0(X0,k3_enumset1(X1,X2,X3,X4,X5))
    | X0 != k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | X1 != sK3
    | X2 != sK3
    | X3 != sK3
    | X4 != sK3
    | X5 != sK3
    | sK2 != sK3 ),
    inference(resolution,[status(thm)],[c_3882,c_1216])).

cnf(c_19066,plain,
    ( r1_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(X0,X1,X2,X3,X4))
    | X0 != sK3
    | X1 != sK3
    | X2 != sK3
    | X3 != sK3
    | X4 != sK3
    | sK2 != sK3 ),
    inference(resolution,[status(thm)],[c_18605,c_15])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_19070,plain,
    ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(X0,X1,X2,X3,X4))
    | X0 != sK3
    | X1 != sK3
    | X2 != sK3
    | X3 != sK3
    | X4 != sK3
    | sK2 != sK3 ),
    inference(resolution,[status(thm)],[c_18605,c_618])).

cnf(c_19072,plain,
    ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_19070])).

cnf(c_19246,plain,
    ( sK2 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19066,c_17,c_19072])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2295,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X0,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(resolution,[status(thm)],[c_0,c_12])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_14,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | sK2 = sK3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1293,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK2 = sK3 ),
    inference(resolution,[status(thm)],[c_7,c_14])).

cnf(c_1301,plain,
    ( r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK2 = sK3 ),
    inference(resolution,[status(thm)],[c_1293,c_12])).

cnf(c_6928,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK2,X0)
    | sK2 = sK3 ),
    inference(resolution,[status(thm)],[c_2295,c_1301])).

cnf(c_19257,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK2,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_19246,c_6928])).

cnf(c_20732,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,X1) ),
    inference(resolution,[status(thm)],[c_5486,c_19257])).

cnf(c_19256,plain,
    ( r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_19246,c_1301])).

cnf(c_25190,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_20732,c_19256])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,plain,
    ( ~ r1_tarski(sK2,sK2)
    | r2_hidden(sK2,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_41,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1129,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1237,plain,
    ( r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1362,plain,
    ( r1_tarski(sK3,X0)
    | ~ r2_hidden(sK3,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1364,plain,
    ( r1_tarski(sK3,sK2)
    | ~ r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_1482,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK3))
    | r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1974,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(X0))
    | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1976,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2))
    | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_3443,plain,
    ( ~ r1_tarski(X0,sK3)
    | r2_hidden(X0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1224,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_enumset1(X2,X2,X2,X2,X2))
    | ~ r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3938,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | ~ r2_hidden(X0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X2)) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_9396,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(X0,k1_zfmisc_1(sK3))
    | ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3938])).

cnf(c_14307,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_3938])).

cnf(c_14309,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK2,k1_zfmisc_1(sK2))
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_14307])).

cnf(c_1418,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(resolution,[status(thm)],[c_13,c_12])).

cnf(c_25188,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_20732,c_1418])).

cnf(c_25686,plain,
    ( ~ r1_tarski(sK3,X0)
    | ~ r1_tarski(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25190,c_17,c_26,c_41,c_1129,c_1237,c_1301,c_1364,c_1482,c_1976,c_3443,c_9396,c_14309,c_19072,c_25188])).

cnf(c_25687,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(renaming,[status(thm)],[c_25686])).

cnf(c_26246,plain,
    ( ~ r1_tarski(sK3,sK3) ),
    inference(resolution,[status(thm)],[c_25687,c_5])).

cnf(c_1354,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26246,c_1354])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.84/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.84/1.50  
% 7.84/1.50  ------  iProver source info
% 7.84/1.50  
% 7.84/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.84/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.84/1.50  git: non_committed_changes: false
% 7.84/1.50  git: last_make_outside_of_git: false
% 7.84/1.50  
% 7.84/1.50  ------ 
% 7.84/1.50  ------ Parsing...
% 7.84/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.84/1.50  ------ Proving...
% 7.84/1.50  ------ Problem Properties 
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  clauses                                 15
% 7.84/1.50  conjectures                             2
% 7.84/1.50  EPR                                     3
% 7.84/1.50  Horn                                    11
% 7.84/1.50  unary                                   2
% 7.84/1.50  binary                                  9
% 7.84/1.50  lits                                    32
% 7.84/1.50  lits eq                                 9
% 7.84/1.50  fd_pure                                 0
% 7.84/1.50  fd_pseudo                               0
% 7.84/1.50  fd_cond                                 0
% 7.84/1.50  fd_pseudo_cond                          3
% 7.84/1.50  AC symbols                              0
% 7.84/1.50  
% 7.84/1.50  ------ Input Options Time Limit: Unbounded
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  ------ 
% 7.84/1.50  Current options:
% 7.84/1.50  ------ 
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  ------ Proving...
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  % SZS status Theorem for theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  fof(f2,axiom,(
% 7.84/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f21,plain,(
% 7.84/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.84/1.50    inference(nnf_transformation,[],[f2])).
% 7.84/1.50  
% 7.84/1.50  fof(f22,plain,(
% 7.84/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.84/1.50    inference(flattening,[],[f21])).
% 7.84/1.50  
% 7.84/1.50  fof(f36,plain,(
% 7.84/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f22])).
% 7.84/1.50  
% 7.84/1.50  fof(f4,axiom,(
% 7.84/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f23,plain,(
% 7.84/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.84/1.50    inference(nnf_transformation,[],[f4])).
% 7.84/1.50  
% 7.84/1.50  fof(f39,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 7.84/1.50    inference(cnf_transformation,[],[f23])).
% 7.84/1.50  
% 7.84/1.50  fof(f3,axiom,(
% 7.84/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f37,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f3])).
% 7.84/1.50  
% 7.84/1.50  fof(f55,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 7.84/1.50    inference(definition_unfolding,[],[f39,f37])).
% 7.84/1.50  
% 7.84/1.50  fof(f12,conjecture,(
% 7.84/1.50    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f13,negated_conjecture,(
% 7.84/1.50    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.84/1.50    inference(negated_conjecture,[],[f12])).
% 7.84/1.50  
% 7.84/1.50  fof(f18,plain,(
% 7.84/1.50    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <~> X0 != X1)),
% 7.84/1.50    inference(ennf_transformation,[],[f13])).
% 7.84/1.50  
% 7.84/1.50  fof(f28,plain,(
% 7.84/1.50    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)))),
% 7.84/1.50    inference(nnf_transformation,[],[f18])).
% 7.84/1.50  
% 7.84/1.50  fof(f29,plain,(
% 7.84/1.50    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))) => ((sK2 = sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2)) & (sK2 != sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)))),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f30,plain,(
% 7.84/1.50    (sK2 = sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2)) & (sK2 != sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 7.84/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f29])).
% 7.84/1.50  
% 7.84/1.50  fof(f50,plain,(
% 7.84/1.50    sK2 != sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 7.84/1.50    inference(cnf_transformation,[],[f30])).
% 7.84/1.50  
% 7.84/1.50  fof(f5,axiom,(
% 7.84/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f40,plain,(
% 7.84/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f5])).
% 7.84/1.50  
% 7.84/1.50  fof(f6,axiom,(
% 7.84/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f41,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f6])).
% 7.84/1.50  
% 7.84/1.50  fof(f7,axiom,(
% 7.84/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f42,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f7])).
% 7.84/1.50  
% 7.84/1.50  fof(f8,axiom,(
% 7.84/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f43,plain,(
% 7.84/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f8])).
% 7.84/1.50  
% 7.84/1.50  fof(f52,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f42,f43])).
% 7.84/1.50  
% 7.84/1.50  fof(f53,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f41,f52])).
% 7.84/1.50  
% 7.84/1.50  fof(f54,plain,(
% 7.84/1.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f40,f53])).
% 7.84/1.50  
% 7.84/1.50  fof(f60,plain,(
% 7.84/1.50    sK2 != sK3 | k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 7.84/1.50    inference(definition_unfolding,[],[f50,f37,f54,f54,f54])).
% 7.84/1.50  
% 7.84/1.50  fof(f11,axiom,(
% 7.84/1.50    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f17,plain,(
% 7.84/1.50    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 7.84/1.50    inference(ennf_transformation,[],[f11])).
% 7.84/1.50  
% 7.84/1.50  fof(f49,plain,(
% 7.84/1.50    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f17])).
% 7.84/1.50  
% 7.84/1.50  fof(f58,plain,(
% 7.84/1.50    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 7.84/1.50    inference(definition_unfolding,[],[f49,f54,f54])).
% 7.84/1.50  
% 7.84/1.50  fof(f65,plain,(
% 7.84/1.50    ( ! [X1] : (~r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 7.84/1.50    inference(equality_resolution,[],[f58])).
% 7.84/1.50  
% 7.84/1.50  fof(f1,axiom,(
% 7.84/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f14,plain,(
% 7.84/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.84/1.50    inference(rectify,[],[f1])).
% 7.84/1.50  
% 7.84/1.50  fof(f15,plain,(
% 7.84/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.84/1.50    inference(ennf_transformation,[],[f14])).
% 7.84/1.50  
% 7.84/1.50  fof(f19,plain,(
% 7.84/1.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f20,plain,(
% 7.84/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.84/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).
% 7.84/1.50  
% 7.84/1.50  fof(f33,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f20])).
% 7.84/1.50  
% 7.84/1.50  fof(f10,axiom,(
% 7.84/1.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f16,plain,(
% 7.84/1.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 7.84/1.50    inference(ennf_transformation,[],[f10])).
% 7.84/1.50  
% 7.84/1.50  fof(f48,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f16])).
% 7.84/1.50  
% 7.84/1.50  fof(f57,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f48,f54])).
% 7.84/1.50  
% 7.84/1.50  fof(f38,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f23])).
% 7.84/1.50  
% 7.84/1.50  fof(f56,plain,(
% 7.84/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.84/1.50    inference(definition_unfolding,[],[f38,f37])).
% 7.84/1.50  
% 7.84/1.50  fof(f51,plain,(
% 7.84/1.50    sK2 = sK3 | k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(sK2)),
% 7.84/1.50    inference(cnf_transformation,[],[f30])).
% 7.84/1.50  
% 7.84/1.50  fof(f59,plain,(
% 7.84/1.50    sK2 = sK3 | k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 7.84/1.50    inference(definition_unfolding,[],[f51,f37,f54,f54,f54])).
% 7.84/1.50  
% 7.84/1.50  fof(f9,axiom,(
% 7.84/1.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f24,plain,(
% 7.84/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.84/1.50    inference(nnf_transformation,[],[f9])).
% 7.84/1.50  
% 7.84/1.50  fof(f25,plain,(
% 7.84/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.84/1.50    inference(rectify,[],[f24])).
% 7.84/1.50  
% 7.84/1.50  fof(f26,plain,(
% 7.84/1.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f27,plain,(
% 7.84/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.84/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 7.84/1.50  
% 7.84/1.50  fof(f45,plain,(
% 7.84/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.84/1.50    inference(cnf_transformation,[],[f27])).
% 7.84/1.50  
% 7.84/1.50  fof(f63,plain,(
% 7.84/1.50    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.84/1.50    inference(equality_resolution,[],[f45])).
% 7.84/1.50  
% 7.84/1.50  fof(f34,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.84/1.50    inference(cnf_transformation,[],[f22])).
% 7.84/1.50  
% 7.84/1.50  fof(f62,plain,(
% 7.84/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.84/1.50    inference(equality_resolution,[],[f34])).
% 7.84/1.50  
% 7.84/1.50  fof(f44,plain,(
% 7.84/1.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.84/1.50    inference(cnf_transformation,[],[f27])).
% 7.84/1.50  
% 7.84/1.50  fof(f64,plain,(
% 7.84/1.50    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.84/1.50    inference(equality_resolution,[],[f44])).
% 7.84/1.50  
% 7.84/1.50  cnf(c_621,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.84/1.50      theory(equality) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_618,plain,( X0 = X0 ),theory(equality) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2711,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_621,c_618]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.84/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_5486,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,X1)
% 7.84/1.50      | ~ r1_tarski(X1,X0)
% 7.84/1.50      | ~ r2_hidden(X0,X2)
% 7.84/1.50      | r2_hidden(X1,X2) ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_2711,c_3]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_625,plain,
% 7.84/1.50      ( X0 != X1
% 7.84/1.50      | X2 != X3
% 7.84/1.50      | X4 != X5
% 7.84/1.50      | X6 != X7
% 7.84/1.50      | X8 != X9
% 7.84/1.50      | k3_enumset1(X0,X2,X4,X6,X8) = k3_enumset1(X1,X3,X5,X7,X9) ),
% 7.84/1.50      theory(equality) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_620,plain,
% 7.84/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.84/1.50      theory(equality) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3882,plain,
% 7.84/1.50      ( ~ r1_xboole_0(X0,k3_enumset1(X1,X2,X3,X4,X5))
% 7.84/1.50      | r1_xboole_0(X6,k3_enumset1(X7,X8,X9,X10,X11))
% 7.84/1.50      | X6 != X0
% 7.84/1.50      | X7 != X1
% 7.84/1.50      | X8 != X2
% 7.84/1.50      | X9 != X3
% 7.84/1.50      | X10 != X4
% 7.84/1.50      | X11 != X5 ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_625,c_620]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_6,plain,
% 7.84/1.50      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 7.84/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_15,negated_conjecture,
% 7.84/1.50      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
% 7.84/1.50      | sK2 != sK3 ),
% 7.84/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1216,plain,
% 7.84/1.50      ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 7.84/1.50      | sK2 != sK3 ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_6,c_15]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_18605,plain,
% 7.84/1.50      ( r1_xboole_0(X0,k3_enumset1(X1,X2,X3,X4,X5))
% 7.84/1.50      | X0 != k3_enumset1(sK2,sK2,sK2,sK2,sK2)
% 7.84/1.50      | X1 != sK3
% 7.84/1.50      | X2 != sK3
% 7.84/1.50      | X3 != sK3
% 7.84/1.50      | X4 != sK3
% 7.84/1.50      | X5 != sK3
% 7.84/1.50      | sK2 != sK3 ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_3882,c_1216]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19066,plain,
% 7.84/1.50      ( r1_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(X0,X1,X2,X3,X4))
% 7.84/1.50      | X0 != sK3
% 7.84/1.50      | X1 != sK3
% 7.84/1.50      | X2 != sK3
% 7.84/1.50      | X3 != sK3
% 7.84/1.50      | X4 != sK3
% 7.84/1.50      | sK2 != sK3 ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_18605,c_15]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_13,plain,
% 7.84/1.50      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) ),
% 7.84/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_17,plain,
% 7.84/1.50      ( ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19070,plain,
% 7.84/1.50      ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(X0,X1,X2,X3,X4))
% 7.84/1.50      | X0 != sK3
% 7.84/1.50      | X1 != sK3
% 7.84/1.50      | X2 != sK3
% 7.84/1.50      | X3 != sK3
% 7.84/1.50      | X4 != sK3
% 7.84/1.50      | sK2 != sK3 ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_18605,c_618]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19072,plain,
% 7.84/1.50      ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 7.84/1.50      | sK2 != sK3 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_19070]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19246,plain,
% 7.84/1.50      ( sK2 != sK3 ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_19066,c_17,c_19072]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_0,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_12,plain,
% 7.84/1.50      ( r2_hidden(X0,X1) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2295,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,X1)
% 7.84/1.50      | r2_hidden(X2,X1)
% 7.84/1.50      | ~ r2_hidden(X0,k3_enumset1(X2,X2,X2,X2,X2)) ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_0,c_12]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_7,plain,
% 7.84/1.50      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 7.84/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_14,negated_conjecture,
% 7.84/1.50      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != k3_enumset1(sK2,sK2,sK2,sK2,sK2)
% 7.84/1.50      | sK2 = sK3 ),
% 7.84/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1293,plain,
% 7.84/1.50      ( ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 7.84/1.50      | sK2 = sK3 ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_7,c_14]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1301,plain,
% 7.84/1.50      ( r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK2 = sK3 ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_1293,c_12]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_6928,plain,
% 7.84/1.50      ( r2_hidden(sK3,X0) | ~ r2_hidden(sK2,X0) | sK2 = sK3 ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_2295,c_1301]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19257,plain,
% 7.84/1.50      ( r2_hidden(sK3,X0) | ~ r2_hidden(sK2,X0) ),
% 7.84/1.50      inference(backward_subsumption_resolution,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_19246,c_6928]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_20732,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,sK3)
% 7.84/1.50      | ~ r1_tarski(sK3,X0)
% 7.84/1.50      | r2_hidden(X0,X1)
% 7.84/1.50      | ~ r2_hidden(sK2,X1) ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_5486,c_19257]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19256,plain,
% 7.84/1.50      ( r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 7.84/1.50      inference(backward_subsumption_resolution,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_19246,c_1301]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_25190,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,sK3)
% 7.84/1.50      | ~ r1_tarski(sK3,X0)
% 7.84/1.50      | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_20732,c_19256]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_10,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.84/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_26,plain,
% 7.84/1.50      ( ~ r1_tarski(sK2,sK2) | r2_hidden(sK2,k1_zfmisc_1(sK2)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_10]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_5,plain,
% 7.84/1.50      ( r1_tarski(X0,X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_41,plain,
% 7.84/1.50      ( r1_tarski(sK2,sK2) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1129,plain,
% 7.84/1.50      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK2 = sK3 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_11,plain,
% 7.84/1.50      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.84/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1237,plain,
% 7.84/1.50      ( r1_tarski(sK2,sK3) | ~ r2_hidden(sK2,k1_zfmisc_1(sK3)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1362,plain,
% 7.84/1.50      ( r1_tarski(sK3,X0) | ~ r2_hidden(sK3,k1_zfmisc_1(X0)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1364,plain,
% 7.84/1.50      ( r1_tarski(sK3,sK2) | ~ r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_1362]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1482,plain,
% 7.84/1.50      ( r2_hidden(sK2,k1_zfmisc_1(sK3))
% 7.84/1.50      | r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(sK3)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1974,plain,
% 7.84/1.50      ( r2_hidden(sK3,k1_zfmisc_1(X0))
% 7.84/1.50      | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_zfmisc_1(X0)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1976,plain,
% 7.84/1.50      ( r2_hidden(sK3,k1_zfmisc_1(sK2))
% 7.84/1.50      | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_zfmisc_1(sK2)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_1974]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3443,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,sK3) | r2_hidden(X0,k1_zfmisc_1(sK3)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_10]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1224,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,X1)
% 7.84/1.50      | ~ r2_hidden(X0,k3_enumset1(X2,X2,X2,X2,X2))
% 7.84/1.50      | ~ r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X1) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3938,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 7.84/1.50      | ~ r2_hidden(X0,k1_zfmisc_1(X2))
% 7.84/1.50      | ~ r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X2)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_1224]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_9396,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 7.84/1.50      | ~ r2_hidden(X0,k1_zfmisc_1(sK3))
% 7.84/1.50      | ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(sK3)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3938]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_14307,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 7.84/1.50      | ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 7.84/1.50      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_zfmisc_1(X1)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3938]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_14309,plain,
% 7.84/1.50      ( ~ r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 7.84/1.50      | ~ r2_hidden(sK2,k1_zfmisc_1(sK2))
% 7.84/1.50      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_zfmisc_1(sK2)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_14307]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1418,plain,
% 7.84/1.50      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_13,c_12]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_25188,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,sK3)
% 7.84/1.50      | ~ r1_tarski(sK3,X0)
% 7.84/1.50      | r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_20732,c_1418]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_25686,plain,
% 7.84/1.50      ( ~ r1_tarski(sK3,X0) | ~ r1_tarski(X0,sK3) ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_25190,c_17,c_26,c_41,c_1129,c_1237,c_1301,c_1364,
% 7.84/1.50                 c_1482,c_1976,c_3443,c_9396,c_14309,c_19072,c_25188]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_25687,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) ),
% 7.84/1.50      inference(renaming,[status(thm)],[c_25686]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_26246,plain,
% 7.84/1.50      ( ~ r1_tarski(sK3,sK3) ),
% 7.84/1.50      inference(resolution,[status(thm)],[c_25687,c_5]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1354,plain,
% 7.84/1.50      ( r1_tarski(sK3,sK3) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(contradiction,plain,
% 7.84/1.50      ( $false ),
% 7.84/1.50      inference(minisat,[status(thm)],[c_26246,c_1354]) ).
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  ------                               Statistics
% 7.84/1.50  
% 7.84/1.50  ------ Selected
% 7.84/1.50  
% 7.84/1.50  total_time:                             0.91
% 7.84/1.50  
%------------------------------------------------------------------------------
