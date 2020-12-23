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
% DateTime   : Thu Dec  3 11:28:58 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 210 expanded)
%              Number of clauses        :   24 (  25 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  273 ( 559 expanded)
%              Number of equality atoms :  191 ( 412 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    9 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK3 != sK4
      & k1_tarski(sK3) = k2_tarski(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( sK3 != sK4
    & k1_tarski(sK3) = k2_tarski(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f28])).

fof(f57,plain,(
    k1_tarski(sK3) = k2_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f63,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f70,plain,(
    k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(definition_unfolding,[],[f57,f64,f63])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(definition_folding,[],[f15,f18,f17])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f49,f59,f64])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f48,f59,f65,f64])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))))) != X9 ) ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))))))) ),
    inference(equality_resolution,[],[f69])).

fof(f24,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X8 != X10
          & X7 != X10
          & X6 != X10
          & X5 != X10
          & X4 != X10
          & X3 != X10
          & X2 != X10
          & X1 != X10
          & X0 != X10 ) )
      & ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10
        | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X8 != X10
          & X7 != X10
          & X6 != X10
          & X5 != X10
          & X4 != X10
          & X3 != X10
          & X2 != X10
          & X1 != X10
          & X0 != X10 ) )
      & ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10
        | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8
          & X0 != X9 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | X0 = X9
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(rectify,[],[f25])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X4 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X4,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f42])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ? [X10] :
            ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ? [X10] :
            ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
          ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X10,X9) )
          & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X10,X9) ) )
     => ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X11,X9)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | X0 = X9
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_18,negated_conjecture,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))))))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1090,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1174,plain,
    ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK5,X0,X1,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1090])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2,X3,X0,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1098,plain,
    ( sP0(X0,X1,X2,X3,X0,X4,X5,X6,X7,X8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
    | r2_hidden(X0,X10) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1103,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
    | sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10) != iProver_top
    | r2_hidden(X0,X10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2121,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
    | r2_hidden(X5,X9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1103])).

cnf(c_14061,plain,
    ( r2_hidden(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_2121])).

cnf(c_14076,plain,
    ( r2_hidden(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14061])).

cnf(c_4,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
    | ~ r2_hidden(X0,X10) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1206,plain,
    ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK3,X8)
    | ~ r2_hidden(sK4,X8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1978,plain,
    ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK3,k5_xboole_0(k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1))))))))
    | ~ r2_hidden(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))))))) ),
    inference(instantiation,[status(thm)],[c_1206])).

cnf(c_1980,plain,
    ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top
    | sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK3,k5_xboole_0(k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))))))) != iProver_top
    | r2_hidden(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1978])).

cnf(c_1982,plain,
    ( sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = iProver_top
    | sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) != iProver_top
    | r2_hidden(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1980])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | X9 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X3 = X0
    | X2 = X0
    | X1 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1149,plain,
    ( ~ sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
    | X7 = sK4
    | X6 = sK4
    | X5 = sK4
    | X4 = sK4
    | X3 = sK4
    | X2 = sK4
    | X1 = sK4
    | X0 = sK4
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1150,plain,
    ( X0 = sK4
    | X1 = sK4
    | X2 = sK4
    | X3 = sK4
    | X4 = sK4
    | X5 = sK4
    | X6 = sK4
    | X7 = sK4
    | sK3 = sK4
    | sP0(sK4,sK3,X7,X6,X5,X4,X3,X2,X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_1152,plain,
    ( sK3 = sK4
    | sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_19,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_21,plain,
    ( sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_17,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14076,c_1982,c_1152,c_21,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.78/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.48  
% 7.78/1.48  ------  iProver source info
% 7.78/1.48  
% 7.78/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.48  git: non_committed_changes: false
% 7.78/1.48  git: last_make_outside_of_git: false
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  ------ Parsing...
% 7.78/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.48  ------ Proving...
% 7.78/1.48  ------ Problem Properties 
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  clauses                                 19
% 7.78/1.48  conjectures                             2
% 7.78/1.48  EPR                                     13
% 7.78/1.48  Horn                                    17
% 7.78/1.48  unary                                   13
% 7.78/1.48  binary                                  1
% 7.78/1.48  lits                                    37
% 7.78/1.48  lits eq                                 13
% 7.78/1.48  fd_pure                                 0
% 7.78/1.48  fd_pseudo                               0
% 7.78/1.48  fd_cond                                 0
% 7.78/1.48  fd_pseudo_cond                          2
% 7.78/1.48  AC symbols                              0
% 7.78/1.48  
% 7.78/1.48  ------ Input Options Time Limit: Unbounded
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  Current options:
% 7.78/1.48  ------ 
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  ------ Proving...
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  % SZS status Theorem for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  fof(f13,conjecture,(
% 7.78/1.48    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f14,negated_conjecture,(
% 7.78/1.48    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 7.78/1.48    inference(negated_conjecture,[],[f13])).
% 7.78/1.48  
% 7.78/1.48  fof(f16,plain,(
% 7.78/1.48    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 7.78/1.48    inference(ennf_transformation,[],[f14])).
% 7.78/1.48  
% 7.78/1.48  fof(f28,plain,(
% 7.78/1.48    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK3 != sK4 & k1_tarski(sK3) = k2_tarski(sK4,sK5))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f29,plain,(
% 7.78/1.48    sK3 != sK4 & k1_tarski(sK3) = k2_tarski(sK4,sK5)),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f28])).
% 7.78/1.48  
% 7.78/1.48  fof(f57,plain,(
% 7.78/1.48    k1_tarski(sK3) = k2_tarski(sK4,sK5)),
% 7.78/1.48    inference(cnf_transformation,[],[f29])).
% 7.78/1.48  
% 7.78/1.48  fof(f6,axiom,(
% 7.78/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f50,plain,(
% 7.78/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f6])).
% 7.78/1.48  
% 7.78/1.48  fof(f64,plain,(
% 7.78/1.48    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f50,f63])).
% 7.78/1.48  
% 7.78/1.48  fof(f7,axiom,(
% 7.78/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f51,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f7])).
% 7.78/1.48  
% 7.78/1.48  fof(f8,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f52,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f8])).
% 7.78/1.48  
% 7.78/1.48  fof(f9,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f53,plain,(
% 7.78/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f9])).
% 7.78/1.48  
% 7.78/1.48  fof(f10,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f54,plain,(
% 7.78/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f10])).
% 7.78/1.48  
% 7.78/1.48  fof(f11,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f55,plain,(
% 7.78/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f11])).
% 7.78/1.48  
% 7.78/1.48  fof(f60,plain,(
% 7.78/1.48    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f54,f55])).
% 7.78/1.48  
% 7.78/1.48  fof(f61,plain,(
% 7.78/1.48    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f53,f60])).
% 7.78/1.48  
% 7.78/1.48  fof(f62,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f52,f61])).
% 7.78/1.48  
% 7.78/1.48  fof(f63,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f51,f62])).
% 7.78/1.48  
% 7.78/1.48  fof(f70,plain,(
% 7.78/1.48    k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),
% 7.78/1.48    inference(definition_unfolding,[],[f57,f64,f63])).
% 7.78/1.48  
% 7.78/1.48  fof(f3,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f15,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 7.78/1.48    inference(ennf_transformation,[],[f3])).
% 7.78/1.48  
% 7.78/1.48  fof(f18,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 7.78/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.78/1.48  
% 7.78/1.48  fof(f17,plain,(
% 7.78/1.48    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10))),
% 7.78/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.78/1.48  
% 7.78/1.48  fof(f19,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))),
% 7.78/1.48    inference(definition_folding,[],[f15,f18,f17])).
% 7.78/1.48  
% 7.78/1.48  fof(f27,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 7.78/1.48    inference(nnf_transformation,[],[f19])).
% 7.78/1.48  
% 7.78/1.48  fof(f46,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 7.78/1.48    inference(cnf_transformation,[],[f27])).
% 7.78/1.48  
% 7.78/1.48  fof(f4,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f48,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f4])).
% 7.78/1.48  
% 7.78/1.48  fof(f5,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f49,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f5])).
% 7.78/1.48  
% 7.78/1.48  fof(f2,axiom,(
% 7.78/1.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f31,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f2])).
% 7.78/1.48  
% 7.78/1.48  fof(f1,axiom,(
% 7.78/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f30,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f1])).
% 7.78/1.48  
% 7.78/1.48  fof(f59,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f31,f30])).
% 7.78/1.48  
% 7.78/1.48  fof(f65,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f49,f59,f64])).
% 7.78/1.48  
% 7.78/1.48  fof(f66,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f48,f59,f65,f64])).
% 7.78/1.48  
% 7.78/1.48  fof(f69,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))))) != X9) )),
% 7.78/1.48    inference(definition_unfolding,[],[f46,f66])).
% 7.78/1.48  
% 7.78/1.48  fof(f80,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))))))) )),
% 7.78/1.48    inference(equality_resolution,[],[f69])).
% 7.78/1.48  
% 7.78/1.48  fof(f24,plain,(
% 7.78/1.48    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 7.78/1.48    inference(nnf_transformation,[],[f17])).
% 7.78/1.48  
% 7.78/1.48  fof(f25,plain,(
% 7.78/1.48    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 7.78/1.48    inference(flattening,[],[f24])).
% 7.78/1.48  
% 7.78/1.48  fof(f26,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 7.78/1.48    inference(rectify,[],[f25])).
% 7.78/1.48  
% 7.78/1.48  fof(f42,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X4) )),
% 7.78/1.48    inference(cnf_transformation,[],[f26])).
% 7.78/1.48  
% 7.78/1.48  fof(f74,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X4,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 7.78/1.48    inference(equality_resolution,[],[f42])).
% 7.78/1.48  
% 7.78/1.48  fof(f20,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 7.78/1.48    inference(nnf_transformation,[],[f18])).
% 7.78/1.48  
% 7.78/1.48  fof(f21,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 7.78/1.48    inference(rectify,[],[f20])).
% 7.78/1.48  
% 7.78/1.48  fof(f22,plain,(
% 7.78/1.48    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f23,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 7.78/1.48  
% 7.78/1.48  fof(f33,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f23])).
% 7.78/1.48  
% 7.78/1.48  fof(f32,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f23])).
% 7.78/1.48  
% 7.78/1.48  fof(f36,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f26])).
% 7.78/1.48  
% 7.78/1.48  fof(f58,plain,(
% 7.78/1.48    sK3 != sK4),
% 7.78/1.48    inference(cnf_transformation,[],[f29])).
% 7.78/1.48  
% 7.78/1.48  cnf(c_18,negated_conjecture,
% 7.78/1.48      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 7.78/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_16,plain,
% 7.78/1.48      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))))))) ),
% 7.78/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1090,plain,
% 7.78/1.48      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))))))) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1174,plain,
% 7.78/1.48      ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK5,X0,X1,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_18,c_1090]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_8,plain,
% 7.78/1.48      ( sP0(X0,X1,X2,X3,X0,X4,X5,X6,X7,X8) ),
% 7.78/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1098,plain,
% 7.78/1.48      ( sP0(X0,X1,X2,X3,X0,X4,X5,X6,X7,X8) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3,plain,
% 7.78/1.48      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 7.78/1.48      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
% 7.78/1.48      | r2_hidden(X0,X10) ),
% 7.78/1.48      inference(cnf_transformation,[],[f33]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1103,plain,
% 7.78/1.48      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
% 7.78/1.48      | sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10) != iProver_top
% 7.78/1.48      | r2_hidden(X0,X10) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2121,plain,
% 7.78/1.48      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
% 7.78/1.48      | r2_hidden(X5,X9) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1098,c_1103]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_14061,plain,
% 7.78/1.48      ( r2_hidden(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1174,c_2121]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_14076,plain,
% 7.78/1.48      ( r2_hidden(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) = iProver_top ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_14061]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_4,plain,
% 7.78/1.48      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 7.78/1.48      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
% 7.78/1.48      | ~ r2_hidden(X0,X10) ),
% 7.78/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1206,plain,
% 7.78/1.48      ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
% 7.78/1.48      | ~ sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK3,X8)
% 7.78/1.48      | ~ r2_hidden(sK4,X8) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_4]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1978,plain,
% 7.78/1.48      ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
% 7.78/1.48      | ~ sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK3,k5_xboole_0(k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1))))))))
% 7.78/1.48      | ~ r2_hidden(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))))))) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1206]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1980,plain,
% 7.78/1.48      ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top
% 7.78/1.48      | sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK3,k5_xboole_0(k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))))))) != iProver_top
% 7.78/1.48      | r2_hidden(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(X7,X6,X5,X4,X3,X2,X1),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X7,X6,X5,X4,X3,X2,X1)))))))) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_1978]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1982,plain,
% 7.78/1.48      ( sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = iProver_top
% 7.78/1.48      | sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) != iProver_top
% 7.78/1.48      | r2_hidden(sK4,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) != iProver_top ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1980]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_14,plain,
% 7.78/1.48      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 7.78/1.48      | X9 = X0
% 7.78/1.48      | X8 = X0
% 7.78/1.48      | X7 = X0
% 7.78/1.48      | X6 = X0
% 7.78/1.48      | X5 = X0
% 7.78/1.48      | X4 = X0
% 7.78/1.48      | X3 = X0
% 7.78/1.48      | X2 = X0
% 7.78/1.48      | X1 = X0 ),
% 7.78/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1149,plain,
% 7.78/1.48      ( ~ sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
% 7.78/1.48      | X7 = sK4
% 7.78/1.48      | X6 = sK4
% 7.78/1.48      | X5 = sK4
% 7.78/1.48      | X4 = sK4
% 7.78/1.48      | X3 = sK4
% 7.78/1.48      | X2 = sK4
% 7.78/1.48      | X1 = sK4
% 7.78/1.48      | X0 = sK4
% 7.78/1.48      | sK3 = sK4 ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1150,plain,
% 7.78/1.48      ( X0 = sK4
% 7.78/1.48      | X1 = sK4
% 7.78/1.48      | X2 = sK4
% 7.78/1.48      | X3 = sK4
% 7.78/1.48      | X4 = sK4
% 7.78/1.48      | X5 = sK4
% 7.78/1.48      | X6 = sK4
% 7.78/1.48      | X7 = sK4
% 7.78/1.48      | sK3 = sK4
% 7.78/1.48      | sP0(sK4,sK3,X7,X6,X5,X4,X3,X2,X1,X0) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_1149]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1152,plain,
% 7.78/1.48      ( sK3 = sK4
% 7.78/1.48      | sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != iProver_top ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1150]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_19,plain,
% 7.78/1.48      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))))))) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_21,plain,
% 7.78/1.48      ( sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))))) = iProver_top ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_17,negated_conjecture,
% 7.78/1.48      ( sK3 != sK4 ),
% 7.78/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(contradiction,plain,
% 7.78/1.48      ( $false ),
% 7.78/1.48      inference(minisat,[status(thm)],[c_14076,c_1982,c_1152,c_21,c_17]) ).
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  ------                               Statistics
% 7.78/1.48  
% 7.78/1.48  ------ Selected
% 7.78/1.48  
% 7.78/1.48  total_time:                             0.751
% 7.78/1.48  
%------------------------------------------------------------------------------
