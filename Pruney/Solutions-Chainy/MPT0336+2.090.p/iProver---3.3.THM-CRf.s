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
% DateTime   : Thu Dec  3 11:38:48 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 254 expanded)
%              Number of clauses        :   43 (  81 expanded)
%              Number of leaves         :   21 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  247 ( 627 expanded)
%              Number of equality atoms :   47 ( 148 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f35,f44,f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f25])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f33])).

fof(f56,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f70,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f56,f44,f61])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f55,f61])).

fof(f59,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f27])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f57,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_229,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2466,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | r2_hidden(X3,k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_229,c_0])).

cnf(c_226,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_225,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2402,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_226,c_225])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3897,plain,
    ( ~ r1_xboole_0(X0,X1)
    | X0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_2402,c_14])).

cnf(c_228,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2454,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_228,c_225])).

cnf(c_4232,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X2)
    | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_3897,c_2454])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1880,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_8,c_13])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1890,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_1880,c_1])).

cnf(c_4716,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X0) ),
    inference(resolution,[status(thm)],[c_4232,c_1890])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4739,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_4716,c_20])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2095,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[status(thm)],[c_15,c_13])).

cnf(c_4755,plain,
    ( r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_4739,c_2095])).

cnf(c_4883,plain,
    ( r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r1_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r1_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_4755,c_4232])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_811,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_847,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_1,c_18])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_951,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1263,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4881,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_4755,c_2])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_6752,plain,
    ( r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r1_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_4881,c_6])).

cnf(c_7093,plain,
    ( r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4883,c_17,c_811,c_847,c_951,c_1263,c_6752])).

cnf(c_11571,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
    | X0 != sK5 ),
    inference(resolution,[status(thm)],[c_2466,c_7093])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1481,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_13336,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(X1,sK3)
    | X0 != sK5 ),
    inference(resolution,[status(thm)],[c_11571,c_1481])).

cnf(c_17601,plain,
    ( ~ r2_hidden(sK5,X0)
    | ~ r1_xboole_0(X0,sK3) ),
    inference(resolution,[status(thm)],[c_13336,c_225])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18749,plain,
    ( ~ r1_xboole_0(sK4,sK3) ),
    inference(resolution,[status(thm)],[c_17601,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18749,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.70/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/1.49  
% 7.70/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.70/1.49  
% 7.70/1.49  ------  iProver source info
% 7.70/1.49  
% 7.70/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.70/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.70/1.49  git: non_committed_changes: false
% 7.70/1.49  git: last_make_outside_of_git: false
% 7.70/1.49  
% 7.70/1.49  ------ 
% 7.70/1.49  ------ Parsing...
% 7.70/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.70/1.49  
% 7.70/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.70/1.49  
% 7.70/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.70/1.49  
% 7.70/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.49  ------ Proving...
% 7.70/1.49  ------ Problem Properties 
% 7.70/1.49  
% 7.70/1.49  
% 7.70/1.49  clauses                                 21
% 7.70/1.49  conjectures                             4
% 7.70/1.49  EPR                                     4
% 7.70/1.49  Horn                                    17
% 7.70/1.49  unary                                   6
% 7.70/1.49  binary                                  13
% 7.70/1.49  lits                                    38
% 7.70/1.49  lits eq                                 7
% 7.70/1.49  fd_pure                                 0
% 7.70/1.49  fd_pseudo                               0
% 7.70/1.49  fd_cond                                 0
% 7.70/1.49  fd_pseudo_cond                          0
% 7.70/1.49  AC symbols                              0
% 7.70/1.49  
% 7.70/1.49  ------ Input Options Time Limit: Unbounded
% 7.70/1.49  
% 7.70/1.49  
% 7.70/1.49  ------ 
% 7.70/1.49  Current options:
% 7.70/1.49  ------ 
% 7.70/1.49  
% 7.70/1.49  
% 7.70/1.49  
% 7.70/1.49  
% 7.70/1.49  ------ Proving...
% 7.70/1.49  
% 7.70/1.49  
% 7.70/1.49  % SZS status Theorem for theBenchmark.p
% 7.70/1.49  
% 7.70/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.70/1.49  
% 7.70/1.49  fof(f1,axiom,(
% 7.70/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f35,plain,(
% 7.70/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.70/1.49    inference(cnf_transformation,[],[f1])).
% 7.70/1.49  
% 7.70/1.49  fof(f7,axiom,(
% 7.70/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f44,plain,(
% 7.70/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.70/1.49    inference(cnf_transformation,[],[f7])).
% 7.70/1.49  
% 7.70/1.49  fof(f62,plain,(
% 7.70/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.70/1.49    inference(definition_unfolding,[],[f35,f44,f44])).
% 7.70/1.49  
% 7.70/1.49  fof(f10,axiom,(
% 7.70/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f31,plain,(
% 7.70/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.70/1.49    inference(nnf_transformation,[],[f10])).
% 7.70/1.49  
% 7.70/1.49  fof(f49,plain,(
% 7.70/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.70/1.49    inference(cnf_transformation,[],[f31])).
% 7.70/1.49  
% 7.70/1.49  fof(f6,axiom,(
% 7.70/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f22,plain,(
% 7.70/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.70/1.49    inference(ennf_transformation,[],[f6])).
% 7.70/1.49  
% 7.70/1.49  fof(f43,plain,(
% 7.70/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.70/1.49    inference(cnf_transformation,[],[f22])).
% 7.70/1.49  
% 7.70/1.49  fof(f66,plain,(
% 7.70/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.70/1.49    inference(definition_unfolding,[],[f43,f44])).
% 7.70/1.49  
% 7.70/1.49  fof(f50,plain,(
% 7.70/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 7.70/1.49    inference(cnf_transformation,[],[f31])).
% 7.70/1.49  
% 7.70/1.49  fof(f2,axiom,(
% 7.70/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f19,plain,(
% 7.70/1.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.70/1.49    inference(ennf_transformation,[],[f2])).
% 7.70/1.49  
% 7.70/1.49  fof(f36,plain,(
% 7.70/1.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.70/1.49    inference(cnf_transformation,[],[f19])).
% 7.70/1.49  
% 7.70/1.49  fof(f15,conjecture,(
% 7.70/1.49    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f16,negated_conjecture,(
% 7.70/1.49    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.70/1.49    inference(negated_conjecture,[],[f15])).
% 7.70/1.49  
% 7.70/1.49  fof(f25,plain,(
% 7.70/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 7.70/1.49    inference(ennf_transformation,[],[f16])).
% 7.70/1.49  
% 7.70/1.49  fof(f26,plain,(
% 7.70/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 7.70/1.49    inference(flattening,[],[f25])).
% 7.70/1.49  
% 7.70/1.49  fof(f33,plain,(
% 7.70/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 7.70/1.49    introduced(choice_axiom,[])).
% 7.70/1.49  
% 7.70/1.49  fof(f34,plain,(
% 7.70/1.49    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.70/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f33])).
% 7.70/1.49  
% 7.70/1.49  fof(f56,plain,(
% 7.70/1.49    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.70/1.49    inference(cnf_transformation,[],[f34])).
% 7.70/1.49  
% 7.70/1.49  fof(f11,axiom,(
% 7.70/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f51,plain,(
% 7.70/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.70/1.49    inference(cnf_transformation,[],[f11])).
% 7.70/1.49  
% 7.70/1.49  fof(f12,axiom,(
% 7.70/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f52,plain,(
% 7.70/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.70/1.49    inference(cnf_transformation,[],[f12])).
% 7.70/1.49  
% 7.70/1.49  fof(f13,axiom,(
% 7.70/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f53,plain,(
% 7.70/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.70/1.49    inference(cnf_transformation,[],[f13])).
% 7.70/1.49  
% 7.70/1.49  fof(f60,plain,(
% 7.70/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.70/1.49    inference(definition_unfolding,[],[f52,f53])).
% 7.70/1.49  
% 7.70/1.49  fof(f61,plain,(
% 7.70/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.70/1.49    inference(definition_unfolding,[],[f51,f60])).
% 7.70/1.49  
% 7.70/1.49  fof(f70,plain,(
% 7.70/1.49    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))),
% 7.70/1.49    inference(definition_unfolding,[],[f56,f44,f61])).
% 7.70/1.49  
% 7.70/1.49  fof(f14,axiom,(
% 7.70/1.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f32,plain,(
% 7.70/1.49    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 7.70/1.49    inference(nnf_transformation,[],[f14])).
% 7.70/1.49  
% 7.70/1.49  fof(f55,plain,(
% 7.70/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.70/1.49    inference(cnf_transformation,[],[f32])).
% 7.70/1.49  
% 7.70/1.49  fof(f68,plain,(
% 7.70/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.70/1.49    inference(definition_unfolding,[],[f55,f61])).
% 7.70/1.49  
% 7.70/1.49  fof(f59,plain,(
% 7.70/1.49    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 7.70/1.49    inference(cnf_transformation,[],[f34])).
% 7.70/1.49  
% 7.70/1.49  fof(f58,plain,(
% 7.70/1.49    r1_xboole_0(sK4,sK3)),
% 7.70/1.49    inference(cnf_transformation,[],[f34])).
% 7.70/1.49  
% 7.70/1.49  fof(f8,axiom,(
% 7.70/1.49    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f23,plain,(
% 7.70/1.49    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.70/1.49    inference(ennf_transformation,[],[f8])).
% 7.70/1.49  
% 7.70/1.49  fof(f45,plain,(
% 7.70/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.70/1.49    inference(cnf_transformation,[],[f23])).
% 7.70/1.49  
% 7.70/1.49  fof(f3,axiom,(
% 7.70/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f17,plain,(
% 7.70/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.70/1.49    inference(rectify,[],[f3])).
% 7.70/1.49  
% 7.70/1.49  fof(f20,plain,(
% 7.70/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.70/1.49    inference(ennf_transformation,[],[f17])).
% 7.70/1.49  
% 7.70/1.49  fof(f27,plain,(
% 7.70/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.70/1.49    introduced(choice_axiom,[])).
% 7.70/1.49  
% 7.70/1.49  fof(f28,plain,(
% 7.70/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.70/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f27])).
% 7.70/1.49  
% 7.70/1.49  fof(f39,plain,(
% 7.70/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.70/1.49    inference(cnf_transformation,[],[f28])).
% 7.70/1.49  
% 7.70/1.49  fof(f4,axiom,(
% 7.70/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f18,plain,(
% 7.70/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.70/1.49    inference(rectify,[],[f4])).
% 7.70/1.49  
% 7.70/1.49  fof(f21,plain,(
% 7.70/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.70/1.49    inference(ennf_transformation,[],[f18])).
% 7.70/1.49  
% 7.70/1.49  fof(f29,plain,(
% 7.70/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.70/1.49    introduced(choice_axiom,[])).
% 7.70/1.49  
% 7.70/1.49  fof(f30,plain,(
% 7.70/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.70/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f29])).
% 7.70/1.49  
% 7.70/1.49  fof(f40,plain,(
% 7.70/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.70/1.49    inference(cnf_transformation,[],[f30])).
% 7.70/1.49  
% 7.70/1.49  fof(f64,plain,(
% 7.70/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 7.70/1.49    inference(definition_unfolding,[],[f40,f44])).
% 7.70/1.49  
% 7.70/1.49  fof(f9,axiom,(
% 7.70/1.49    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 7.70/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.49  
% 7.70/1.49  fof(f24,plain,(
% 7.70/1.49    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 7.70/1.49    inference(ennf_transformation,[],[f9])).
% 7.70/1.49  
% 7.70/1.49  fof(f48,plain,(
% 7.70/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 7.70/1.49    inference(cnf_transformation,[],[f24])).
% 7.70/1.49  
% 7.70/1.49  fof(f67,plain,(
% 7.70/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 7.70/1.49    inference(definition_unfolding,[],[f48,f44])).
% 7.70/1.49  
% 7.70/1.49  fof(f57,plain,(
% 7.70/1.49    r2_hidden(sK5,sK4)),
% 7.70/1.49    inference(cnf_transformation,[],[f34])).
% 7.70/1.49  
% 7.70/1.49  cnf(c_229,plain,
% 7.70/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.70/1.49      theory(equality) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_0,plain,
% 7.70/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.70/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_2466,plain,
% 7.70/1.49      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.70/1.49      | r2_hidden(X3,k4_xboole_0(X2,k4_xboole_0(X2,X1)))
% 7.70/1.49      | X3 != X0 ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_229,c_0]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_226,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_225,plain,( X0 = X0 ),theory(equality) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_2402,plain,
% 7.70/1.49      ( X0 != X1 | X1 = X0 ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_226,c_225]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_14,plain,
% 7.70/1.49      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.70/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_3897,plain,
% 7.70/1.49      ( ~ r1_xboole_0(X0,X1) | X0 = k4_xboole_0(X0,X1) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_2402,c_14]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_228,plain,
% 7.70/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.70/1.49      theory(equality) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_2454,plain,
% 7.70/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_228,c_225]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_4232,plain,
% 7.70/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.70/1.49      | r1_xboole_0(X0,X2)
% 7.70/1.49      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_3897,c_2454]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_8,plain,
% 7.70/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.70/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_13,plain,
% 7.70/1.49      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 7.70/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_1880,plain,
% 7.70/1.49      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_8,c_13]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_1,plain,
% 7.70/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.70/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_1890,plain,
% 7.70/1.49      ( ~ r1_tarski(X0,X1) | r1_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_1880,c_1]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_4716,plain,
% 7.70/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,X0) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_4232,c_1890]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_20,negated_conjecture,
% 7.70/1.49      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.70/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_4739,plain,
% 7.70/1.49      ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.70/1.49      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_4716,c_20]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_15,plain,
% 7.70/1.49      ( r2_hidden(X0,X1)
% 7.70/1.49      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 7.70/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_2095,plain,
% 7.70/1.49      ( r2_hidden(X0,X1) | r1_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_15,c_13]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_4755,plain,
% 7.70/1.49      ( r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 7.70/1.49      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_4739,c_2095]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_4883,plain,
% 7.70/1.49      ( r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 7.70/1.49      | r1_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 7.70/1.49      | ~ r1_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_4755,c_4232]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_17,negated_conjecture,
% 7.70/1.49      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 7.70/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_811,plain,
% 7.70/1.49      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 7.70/1.49      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 7.70/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_18,negated_conjecture,
% 7.70/1.49      ( r1_xboole_0(sK4,sK3) ),
% 7.70/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_847,plain,
% 7.70/1.49      ( r1_xboole_0(sK3,sK4) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_1,c_18]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_11,plain,
% 7.70/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.70/1.49      | ~ r1_xboole_0(X0,X2)
% 7.70/1.49      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.70/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_951,plain,
% 7.70/1.49      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 7.70/1.49      | ~ r1_xboole_0(sK3,sK4)
% 7.70/1.49      | ~ r1_xboole_0(sK3,sK2) ),
% 7.70/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_1263,plain,
% 7.70/1.49      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 7.70/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_2,plain,
% 7.70/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.70/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_4881,plain,
% 7.70/1.49      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 7.70/1.49      | r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_4755,c_2]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_6,plain,
% 7.70/1.49      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 7.70/1.49      | r1_xboole_0(X0,X1) ),
% 7.70/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_6752,plain,
% 7.70/1.49      ( r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 7.70/1.49      | r1_xboole_0(sK2,sK3) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_4881,c_6]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_7093,plain,
% 7.70/1.49      ( r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 7.70/1.49      inference(global_propositional_subsumption,
% 7.70/1.49                [status(thm)],
% 7.70/1.49                [c_4883,c_17,c_811,c_847,c_951,c_1263,c_6752]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_11571,plain,
% 7.70/1.49      ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) | X0 != sK5 ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_2466,c_7093]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_12,plain,
% 7.70/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.70/1.49      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.70/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_1481,plain,
% 7.70/1.49      ( ~ r2_hidden(X0,X1)
% 7.70/1.49      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
% 7.70/1.49      | ~ r1_xboole_0(X1,X2) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_13336,plain,
% 7.70/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(X1,sK3) | X0 != sK5 ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_11571,c_1481]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_17601,plain,
% 7.70/1.49      ( ~ r2_hidden(sK5,X0) | ~ r1_xboole_0(X0,sK3) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_13336,c_225]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_19,negated_conjecture,
% 7.70/1.49      ( r2_hidden(sK5,sK4) ),
% 7.70/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(c_18749,plain,
% 7.70/1.49      ( ~ r1_xboole_0(sK4,sK3) ),
% 7.70/1.49      inference(resolution,[status(thm)],[c_17601,c_19]) ).
% 7.70/1.49  
% 7.70/1.49  cnf(contradiction,plain,
% 7.70/1.49      ( $false ),
% 7.70/1.49      inference(minisat,[status(thm)],[c_18749,c_18]) ).
% 7.70/1.49  
% 7.70/1.49  
% 7.70/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.70/1.49  
% 7.70/1.49  ------                               Statistics
% 7.70/1.49  
% 7.70/1.49  ------ Selected
% 7.70/1.49  
% 7.70/1.49  total_time:                             0.652
% 7.70/1.49  
%------------------------------------------------------------------------------
