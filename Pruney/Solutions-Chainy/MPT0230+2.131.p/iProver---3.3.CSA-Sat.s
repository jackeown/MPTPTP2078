%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:59 EST 2020

% Result     : CounterSatisfiable 3.72s
% Output     : Saturation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  163 (20212 expanded)
%              Number of clauses        :  100 (2226 expanded)
%              Number of leaves         :   24 (6409 expanded)
%              Depth                    :   21
%              Number of atoms          :  475 (28512 expanded)
%              Number of equality atoms :  421 (26240 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    6 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f67])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f48,f39,f66,f68,f67])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34])).

fof(f62,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f49,f63,f64,f67])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f50,f63,f67,f58])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f46,f63,f68,f69])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f47,f63,f67,f70])).

fof(f60,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f60,f68,f67])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f61,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_72,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_71,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_90,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_3,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2648,plain,
    ( ~ iProver_ARSWP_43
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_2749,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2648])).

cnf(c_14,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2960,plain,
    ( ~ iProver_ARSWP_43
    | X0 = sK3
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_2648])).

cnf(c_2961,plain,
    ( X0 = sK3
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK1 = sK3
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2960])).

cnf(c_2963,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK1 = sK3
    | iProver_ARSWP_43 != iProver_top ),
    inference(instantiation,[status(thm)],[c_2961])).

cnf(c_3078,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2749,c_14,c_2963])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2644,plain,
    ( ~ iProver_ARSWP_39
    | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_2753,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_39 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2644])).

cnf(c_3085,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_2753])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3089,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3085,c_6])).

cnf(c_3108,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_3078])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2647,plain,
    ( ~ iProver_ARSWP_42
    | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_2750,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_42 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2647])).

cnf(c_3677,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_2750])).

cnf(c_3709,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3677,c_6])).

cnf(c_3728,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_3709])).

cnf(c_3729,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3709,c_2750])).

cnf(c_6114,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3728,c_3729])).

cnf(c_9951,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3108,c_6114])).

cnf(c_3111,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_2753])).

cnf(c_3682,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_2750])).

cnf(c_6066,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3111,c_3682])).

cnf(c_8379,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_6066])).

cnf(c_9469,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_8379])).

cnf(c_8374,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_6066])).

cnf(c_8429,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8374,c_6])).

cnf(c_8383,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_6066,c_2750])).

cnf(c_8385,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_6066,c_2753])).

cnf(c_8382,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_6066,c_3709])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2650,negated_conjecture,
    ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0)
    | ~ iProver_ARSWP_45 ),
    inference(arg_filter_abstr,[status(unp)],[c_16])).

cnf(c_2747,plain,
    ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) = iProver_top
    | iProver_ARSWP_45 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2650])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2645,plain,
    ( ~ arAF0_r1_tarski_0_1(X0)
    | ~ iProver_ARSWP_40
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_4])).

cnf(c_2752,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X0) != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2645])).

cnf(c_3032,plain,
    ( arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_2747,c_2752])).

cnf(c_3084,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3032,c_3078])).

cnf(c_3097,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3084,c_6])).

cnf(c_3226,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_3032])).

cnf(c_3726,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3032,c_3709])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3769,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3726,c_5,c_6])).

cnf(c_3960,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_3769])).

cnf(c_3681,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_2750])).

cnf(c_5719,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3960,c_3681])).

cnf(c_7094,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5719,c_3709])).

cnf(c_8087,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_7094])).

cnf(c_3230,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_2747])).

cnf(c_3403,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3230,c_2752])).

cnf(c_5724,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3403,c_3681])).

cnf(c_5741,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5724,c_5])).

cnf(c_7093,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5719,c_5741])).

cnf(c_7388,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_7093])).

cnf(c_7087,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_5719])).

cnf(c_7156,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7087,c_6])).

cnf(c_7090,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3032,c_5719])).

cnf(c_7145,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7090,c_5,c_6])).

cnf(c_7095,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5719,c_2750])).

cnf(c_5943,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5741,c_2750])).

cnf(c_6309,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_5943])).

cnf(c_3224,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_3078])).

cnf(c_6306,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3224,c_5943])).

cnf(c_6121,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3729])).

cnf(c_6068,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3108,c_3682])).

cnf(c_3723,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_3709])).

cnf(c_3778,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3723,c_6])).

cnf(c_3907,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_3778])).

cnf(c_6063,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3907,c_3682])).

cnf(c_5725,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3681])).

cnf(c_5722,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3224,c_3681])).

cnf(c_3727,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_3709])).

cnf(c_5175,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3727])).

cnf(c_5717,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5175,c_3681])).

cnf(c_5212,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3224,c_5175])).

cnf(c_5215,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_5175])).

cnf(c_5529,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5212,c_5215])).

cnf(c_4980,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3108,c_3907])).

cnf(c_4667,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3960])).

cnf(c_3906,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_3778])).

cnf(c_4504,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3906])).

cnf(c_4501,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3224,c_3906])).

cnf(c_4155,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3224])).

cnf(c_3964,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3769])).

cnf(c_3910,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3778])).

cnf(c_3731,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3709,c_2753])).

cnf(c_3410,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3111])).

cnf(c_3326,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3108,c_3111])).

cnf(c_3114,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_2747])).

cnf(c_15,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f61])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:25:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.72/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.99  
% 3.72/0.99  ------  iProver source info
% 3.72/0.99  
% 3.72/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.99  git: non_committed_changes: false
% 3.72/0.99  git: last_make_outside_of_git: false
% 3.72/0.99  
% 3.72/0.99  ------ 
% 3.72/0.99  ------ Parsing...
% 3.72/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  ------ Proving...
% 3.72/0.99  ------ Problem Properties 
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  clauses                                 14
% 3.72/0.99  conjectures                             3
% 3.72/0.99  EPR                                     2
% 3.72/0.99  Horn                                    13
% 3.72/0.99  unary                                   12
% 3.72/0.99  binary                                  1
% 3.72/0.99  lits                                    17
% 3.72/0.99  lits eq                                 15
% 3.72/0.99  fd_pure                                 0
% 3.72/0.99  fd_pseudo                               0
% 3.72/0.99  fd_cond                                 0
% 3.72/0.99  fd_pseudo_cond                          1
% 3.72/0.99  AC symbols                              0
% 3.72/0.99  
% 3.72/0.99  ------ Input Options Time Limit: Unbounded
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.72/0.99  Current options:
% 3.72/0.99  ------ 
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  % SZS output start Saturation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  fof(f3,axiom,(
% 3.72/0.99    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f38,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f3])).
% 3.72/0.99  
% 3.72/0.99  fof(f2,axiom,(
% 3.72/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f27,plain,(
% 3.72/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(rectify,[],[f2])).
% 3.72/0.99  
% 3.72/0.99  fof(f28,plain,(
% 3.72/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(ennf_transformation,[],[f27])).
% 3.72/0.99  
% 3.72/0.99  fof(f32,plain,(
% 3.72/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f33,plain,(
% 3.72/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).
% 3.72/0.99  
% 3.72/0.99  fof(f36,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f33])).
% 3.72/0.99  
% 3.72/0.99  fof(f37,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f33])).
% 3.72/0.99  
% 3.72/0.99  fof(f13,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f30,plain,(
% 3.72/0.99    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.72/0.99    inference(ennf_transformation,[],[f13])).
% 3.72/0.99  
% 3.72/0.99  fof(f48,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.72/0.99    inference(cnf_transformation,[],[f30])).
% 3.72/0.99  
% 3.72/0.99  fof(f4,axiom,(
% 3.72/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f39,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f4])).
% 3.72/0.99  
% 3.72/0.99  fof(f18,axiom,(
% 3.72/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f53,plain,(
% 3.72/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f18])).
% 3.72/0.99  
% 3.72/0.99  fof(f68,plain,(
% 3.72/0.99    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f53,f67])).
% 3.72/0.99  
% 3.72/0.99  fof(f19,axiom,(
% 3.72/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f54,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f19])).
% 3.72/0.99  
% 3.72/0.99  fof(f20,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f55,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f20])).
% 3.72/0.99  
% 3.72/0.99  fof(f21,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f56,plain,(
% 3.72/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f21])).
% 3.72/0.99  
% 3.72/0.99  fof(f22,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f57,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f22])).
% 3.72/0.99  
% 3.72/0.99  fof(f23,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f58,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f23])).
% 3.72/0.99  
% 3.72/0.99  fof(f64,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f57,f58])).
% 3.72/0.99  
% 3.72/0.99  fof(f65,plain,(
% 3.72/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f56,f64])).
% 3.72/0.99  
% 3.72/0.99  fof(f66,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f55,f65])).
% 3.72/0.99  
% 3.72/0.99  fof(f67,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f54,f66])).
% 3.72/0.99  
% 3.72/0.99  fof(f75,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.72/0.99    inference(definition_unfolding,[],[f48,f39,f66,f68,f67])).
% 3.72/0.99  
% 3.72/0.99  fof(f25,conjecture,(
% 3.72/0.99    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f26,negated_conjecture,(
% 3.72/0.99    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.72/0.99    inference(negated_conjecture,[],[f25])).
% 3.72/0.99  
% 3.72/0.99  fof(f31,plain,(
% 3.72/0.99    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.72/0.99    inference(ennf_transformation,[],[f26])).
% 3.72/0.99  
% 3.72/0.99  fof(f34,plain,(
% 3.72/0.99    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f35,plain,(
% 3.72/0.99    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34])).
% 3.72/0.99  
% 3.72/0.99  fof(f62,plain,(
% 3.72/0.99    sK1 != sK3),
% 3.72/0.99    inference(cnf_transformation,[],[f35])).
% 3.72/0.99  
% 3.72/0.99  fof(f14,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f49,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f14])).
% 3.72/0.99  
% 3.72/0.99  fof(f8,axiom,(
% 3.72/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f43,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f8])).
% 3.72/0.99  
% 3.72/0.99  fof(f63,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f43,f39])).
% 3.72/0.99  
% 3.72/0.99  fof(f71,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f49,f63,f64,f67])).
% 3.72/0.99  
% 3.72/0.99  fof(f7,axiom,(
% 3.72/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f42,plain,(
% 3.72/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.72/0.99    inference(cnf_transformation,[],[f7])).
% 3.72/0.99  
% 3.72/0.99  fof(f12,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f47,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f12])).
% 3.72/0.99  
% 3.72/0.99  fof(f11,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f46,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f11])).
% 3.72/0.99  
% 3.72/0.99  fof(f15,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f50,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f15])).
% 3.72/0.99  
% 3.72/0.99  fof(f69,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f50,f63,f67,f58])).
% 3.72/0.99  
% 3.72/0.99  fof(f70,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f46,f63,f68,f69])).
% 3.72/0.99  
% 3.72/0.99  fof(f74,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) )),
% 3.72/0.99    inference(definition_unfolding,[],[f47,f63,f67,f70])).
% 3.72/0.99  
% 3.72/0.99  fof(f60,plain,(
% 3.72/0.99    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 3.72/0.99    inference(cnf_transformation,[],[f35])).
% 3.72/0.99  
% 3.72/0.99  fof(f79,plain,(
% 3.72/0.99    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 3.72/0.99    inference(definition_unfolding,[],[f60,f68,f67])).
% 3.72/0.99  
% 3.72/0.99  fof(f5,axiom,(
% 3.72/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f29,plain,(
% 3.72/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.72/0.99    inference(ennf_transformation,[],[f5])).
% 3.72/0.99  
% 3.72/0.99  fof(f40,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f29])).
% 3.72/0.99  
% 3.72/0.99  fof(f6,axiom,(
% 3.72/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f41,plain,(
% 3.72/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.72/0.99    inference(cnf_transformation,[],[f6])).
% 3.72/0.99  
% 3.72/0.99  fof(f61,plain,(
% 3.72/0.99    sK1 != sK2),
% 3.72/0.99    inference(cnf_transformation,[],[f35])).
% 3.72/0.99  
% 3.72/0.99  cnf(c_72,plain,
% 3.72/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.72/0.99      theory(equality) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_71,plain,
% 3.72/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.72/0.99      theory(equality) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_90,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3,plain,
% 3.72/0.99      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2,plain,
% 3.72/0.99      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1,plain,
% 3.72/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.72/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_10,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | X2 = X1
% 3.72/0.99      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
% 3.72/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2648,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_43
% 3.72/0.99      | X0 = X1
% 3.72/0.99      | X2 = X1
% 3.72/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0 ),
% 3.72/0.99      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2749,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | X2 = X1
% 3.72/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2648]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_14,negated_conjecture,
% 3.72/0.99      ( sK1 != sK3 ),
% 3.72/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2960,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_43
% 3.72/0.99      | X0 = sK3
% 3.72/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.72/0.99      | sK1 = sK3 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_2648]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2961,plain,
% 3.72/0.99      ( X0 = sK3
% 3.72/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.72/0.99      | sK1 = sK3
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2960]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2963,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.72/0.99      | sK1 = sK3
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_2961]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3078,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_2749,c_14,c_2963]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_0,plain,
% 3.72/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.72/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2644,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_39
% 3.72/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0 ),
% 3.72/0.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2753,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2644]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3085,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3078,c_2753]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6,plain,
% 3.72/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3089,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_3085,c_6]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3108,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3089,c_3078]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_9,plain,
% 3.72/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
% 3.72/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2647,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_42
% 3.72/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) ),
% 3.72/0.99      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2750,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2647]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3677,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3078,c_2750]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3709,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_3677,c_6]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3728,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3089,c_3709]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3729,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3709,c_2750]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6114,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3728,c_3729]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_9951,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3108,c_6114]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3111,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3089,c_2753]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3682,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3089,c_2750]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6066,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3111,c_3682]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8379,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3089,c_6066]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_9469,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3078,c_8379]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8374,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3078,c_6066]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8429,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_8374,c_6]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8383,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6066,c_2750]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8385,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6066,c_2753]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8382,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6066,c_3709]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_16,negated_conjecture,
% 3.72/0.99      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2650,negated_conjecture,
% 3.72/0.99      ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) | ~ iProver_ARSWP_45 ),
% 3.72/0.99      inference(arg_filter_abstr,[status(unp)],[c_16]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2747,plain,
% 3.72/0.99      ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) = iProver_top
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2650]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4,plain,
% 3.72/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2645,plain,
% 3.72/0.99      ( ~ arAF0_r1_tarski_0_1(X0)
% 3.72/0.99      | ~ iProver_ARSWP_40
% 3.72/0.99      | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.72/0.99      inference(arg_filter_abstr,[status(unp)],[c_4]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2752,plain,
% 3.72/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.72/0.99      | arAF0_r1_tarski_0_1(X0) != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2645]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3032,plain,
% 3.72/0.99      ( arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2747,c_2752]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3084,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3032,c_3078]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3097,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_3084,c_6]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3226,plain,
% 3.72/0.99      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3097,c_3032]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3726,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3032,c_3709]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5,plain,
% 3.72/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3769,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_3726,c_5,c_6]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3960,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3097,c_3769]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3681,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3097,c_2750]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5719,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3960,c_3681]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7094,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_5719,c_3709]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8087,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_7094]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3230,plain,
% 3.72/0.99      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3097,c_2747]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3403,plain,
% 3.72/0.99      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3230,c_2752]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5724,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3403,c_3681]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5741,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_5724,c_5]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7093,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_5719,c_5741]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7388,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3078,c_7093]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7087,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3078,c_5719]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7156,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_7087,c_6]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7090,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3032,c_5719]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7145,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_7090,c_5,c_6]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7095,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_5719,c_2750]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5943,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_5741,c_2750]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6309,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_5943]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3224,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3097,c_3078]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6306,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3224,c_5943]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6121,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_3729]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6068,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3108,c_3682]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3723,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3078,c_3709]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3778,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_3723,c_6]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3907,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3089,c_3778]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6063,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3907,c_3682]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5725,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_3681]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5722,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3224,c_3681]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3727,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3097,c_3709]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5175,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_3727]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5717,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_5175,c_3681]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5212,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3224,c_5175]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5215,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_5175]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5529,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_5212,c_5215]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4980,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3108,c_3907]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4667,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_3960]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3906,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3097,c_3778]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4504,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_3906]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4501,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3224,c_3906]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4155,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_3224]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3964,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_3769]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3910,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_3778]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3731,plain,
% 3.72/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_42 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3709,c_2753]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3410,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_40 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3226,c_3111]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3326,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3108,c_3111]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3114,plain,
% 3.72/0.99      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.72/0.99      | iProver_ARSWP_45 != iProver_top
% 3.72/0.99      | iProver_ARSWP_43 != iProver_top
% 3.72/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3089,c_2747]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_15,negated_conjecture,
% 3.72/0.99      ( sK1 != sK2 ),
% 3.72/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS output end Saturation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  ------                               Statistics
% 3.72/0.99  
% 3.72/0.99  ------ Selected
% 3.72/0.99  
% 3.72/0.99  total_time:                             0.356
% 3.72/0.99  
%------------------------------------------------------------------------------
