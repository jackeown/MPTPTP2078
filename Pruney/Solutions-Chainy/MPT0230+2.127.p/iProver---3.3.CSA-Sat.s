%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:58 EST 2020

% Result     : CounterSatisfiable 3.92s
% Output     : Saturation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  163 (20167 expanded)
%              Number of clauses        :  100 (2226 expanded)
%              Number of leaves         :   24 (6409 expanded)
%              Depth                    :   21
%              Number of atoms          :  475 (28467 expanded)
%              Number of equality atoms :  421 (26195 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    6 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f20,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f72])).

fof(f21,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f23])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f24])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f52,f41,f71,f73,f72])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36])).

fof(f66,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f53,f67,f62,f73])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f46,f67,f69,f69])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f49,f67,f73,f70])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f50,f67,f68,f69,f74])).

fof(f64,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f64,f73,f72])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_74,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_73,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_92,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_3,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2650,plain,
    ( ~ iProver_ARSWP_43
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_2751,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2650])).

cnf(c_16,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2962,plain,
    ( ~ iProver_ARSWP_43
    | X0 = sK3
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_2650])).

cnf(c_2963,plain,
    ( X0 = sK3
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK1 = sK3
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2962])).

cnf(c_2965,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK1 = sK3
    | iProver_ARSWP_43 != iProver_top ),
    inference(instantiation,[status(thm)],[c_2963])).

cnf(c_3080,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2751,c_16,c_2965])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2646,plain,
    ( ~ iProver_ARSWP_39
    | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_2755,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_39 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2646])).

cnf(c_3087,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_2755])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3091,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3087,c_6])).

cnf(c_3110,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_3080])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2649,plain,
    ( ~ iProver_ARSWP_42
    | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_2752,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_42 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2649])).

cnf(c_3679,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_2752])).

cnf(c_3711,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3679,c_6])).

cnf(c_3730,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_3711])).

cnf(c_3731,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3711,c_2752])).

cnf(c_6116,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3730,c_3731])).

cnf(c_9953,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3110,c_6116])).

cnf(c_3113,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_2755])).

cnf(c_3684,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_2752])).

cnf(c_6068,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3113,c_3684])).

cnf(c_8381,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_6068])).

cnf(c_9471,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_8381])).

cnf(c_8376,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_6068])).

cnf(c_8431,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8376,c_6])).

cnf(c_8385,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_6068,c_2752])).

cnf(c_8387,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_6068,c_2755])).

cnf(c_8384,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_6068,c_3711])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2652,negated_conjecture,
    ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0)
    | ~ iProver_ARSWP_45 ),
    inference(arg_filter_abstr,[status(unp)],[c_18])).

cnf(c_2749,plain,
    ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) = iProver_top
    | iProver_ARSWP_45 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2652])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2647,plain,
    ( ~ arAF0_r1_tarski_0_1(X0)
    | ~ iProver_ARSWP_40
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_4])).

cnf(c_2754,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X0) != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2647])).

cnf(c_3034,plain,
    ( arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_2749,c_2754])).

cnf(c_3086,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_3080])).

cnf(c_3099,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3086,c_6])).

cnf(c_3228,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_3034])).

cnf(c_3728,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_3711])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3771,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3728,c_5,c_6])).

cnf(c_3962,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_3771])).

cnf(c_3683,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_2752])).

cnf(c_5721,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3962,c_3683])).

cnf(c_7096,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5721,c_3711])).

cnf(c_8089,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_7096])).

cnf(c_3232,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_2749])).

cnf(c_3405,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3232,c_2754])).

cnf(c_5726,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3405,c_3683])).

cnf(c_5743,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5726,c_5])).

cnf(c_7095,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5721,c_5743])).

cnf(c_7390,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_7095])).

cnf(c_7089,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_5721])).

cnf(c_7158,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7089,c_6])).

cnf(c_7092,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_5721])).

cnf(c_7147,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7092,c_5,c_6])).

cnf(c_7097,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5721,c_2752])).

cnf(c_5945,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5743,c_2752])).

cnf(c_6311,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_5945])).

cnf(c_3226,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_3080])).

cnf(c_6308,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_5945])).

cnf(c_6123,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_3731])).

cnf(c_6070,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3110,c_3684])).

cnf(c_3725,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_3711])).

cnf(c_3780,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3725,c_6])).

cnf(c_3909,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_3780])).

cnf(c_6065,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3909,c_3684])).

cnf(c_5727,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_3683])).

cnf(c_5724,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3683])).

cnf(c_3729,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_3711])).

cnf(c_5177,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_3729])).

cnf(c_5719,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5177,c_3683])).

cnf(c_5214,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_5177])).

cnf(c_5217,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_5177])).

cnf(c_5531,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_5214,c_5217])).

cnf(c_4982,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3110,c_3909])).

cnf(c_4669,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_3962])).

cnf(c_3908,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_3780])).

cnf(c_4506,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_3908])).

cnf(c_4503,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_3908])).

cnf(c_4157,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_3226])).

cnf(c_3966,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_3771])).

cnf(c_3912,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_3780])).

cnf(c_3733,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3711,c_2755])).

cnf(c_3412,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_3113])).

cnf(c_3328,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3110,c_3113])).

cnf(c_3116,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_45 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_2749])).

cnf(c_17,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f65])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.92/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/0.99  
% 3.92/0.99  ------  iProver source info
% 3.92/0.99  
% 3.92/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.92/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/0.99  git: non_committed_changes: false
% 3.92/0.99  git: last_make_outside_of_git: false
% 3.92/0.99  
% 3.92/0.99  ------ 
% 3.92/0.99  ------ Parsing...
% 3.92/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  ------ Proving...
% 3.92/0.99  ------ Problem Properties 
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  clauses                                 16
% 3.92/0.99  conjectures                             3
% 3.92/0.99  EPR                                     2
% 3.92/0.99  Horn                                    15
% 3.92/0.99  unary                                   14
% 3.92/0.99  binary                                  1
% 3.92/0.99  lits                                    19
% 3.92/0.99  lits eq                                 17
% 3.92/0.99  fd_pure                                 0
% 3.92/0.99  fd_pseudo                               0
% 3.92/0.99  fd_cond                                 0
% 3.92/0.99  fd_pseudo_cond                          1
% 3.92/0.99  AC symbols                              0
% 3.92/0.99  
% 3.92/0.99  ------ Input Options Time Limit: Unbounded
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.92/0.99  Current options:
% 3.92/0.99  ------ 
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  % SZS output start Saturation for theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  fof(f3,axiom,(
% 3.92/0.99    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f40,plain,(
% 3.92/0.99    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.92/0.99    inference(cnf_transformation,[],[f3])).
% 3.92/0.99  
% 3.92/0.99  fof(f2,axiom,(
% 3.92/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f29,plain,(
% 3.92/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.92/0.99    inference(rectify,[],[f2])).
% 3.92/0.99  
% 3.92/0.99  fof(f30,plain,(
% 3.92/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.92/0.99    inference(ennf_transformation,[],[f29])).
% 3.92/0.99  
% 3.92/0.99  fof(f34,plain,(
% 3.92/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f35,plain,(
% 3.92/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f34])).
% 3.92/0.99  
% 3.92/0.99  fof(f38,plain,(
% 3.92/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f35])).
% 3.92/0.99  
% 3.92/0.99  fof(f39,plain,(
% 3.92/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.92/0.99    inference(cnf_transformation,[],[f35])).
% 3.92/0.99  
% 3.92/0.99  fof(f15,axiom,(
% 3.92/0.99    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f32,plain,(
% 3.92/0.99    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.92/0.99    inference(ennf_transformation,[],[f15])).
% 3.92/0.99  
% 3.92/0.99  fof(f52,plain,(
% 3.92/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.92/0.99    inference(cnf_transformation,[],[f32])).
% 3.92/0.99  
% 3.92/0.99  fof(f4,axiom,(
% 3.92/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f41,plain,(
% 3.92/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f4])).
% 3.92/0.99  
% 3.92/0.99  fof(f20,axiom,(
% 3.92/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f57,plain,(
% 3.92/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f20])).
% 3.92/0.99  
% 3.92/0.99  fof(f73,plain,(
% 3.92/0.99    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.92/0.99    inference(definition_unfolding,[],[f57,f72])).
% 3.92/0.99  
% 3.92/0.99  fof(f21,axiom,(
% 3.92/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f58,plain,(
% 3.92/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f21])).
% 3.92/0.99  
% 3.92/0.99  fof(f22,axiom,(
% 3.92/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f59,plain,(
% 3.92/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f22])).
% 3.92/0.99  
% 3.92/0.99  fof(f23,axiom,(
% 3.92/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f60,plain,(
% 3.92/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f23])).
% 3.92/0.99  
% 3.92/0.99  fof(f24,axiom,(
% 3.92/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f61,plain,(
% 3.92/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f24])).
% 3.92/0.99  
% 3.92/0.99  fof(f25,axiom,(
% 3.92/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f62,plain,(
% 3.92/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f25])).
% 3.92/0.99  
% 3.92/0.99  fof(f68,plain,(
% 3.92/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.92/0.99    inference(definition_unfolding,[],[f61,f62])).
% 3.92/0.99  
% 3.92/0.99  fof(f69,plain,(
% 3.92/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.92/0.99    inference(definition_unfolding,[],[f60,f68])).
% 3.92/0.99  
% 3.92/0.99  fof(f71,plain,(
% 3.92/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.92/0.99    inference(definition_unfolding,[],[f59,f69])).
% 3.92/0.99  
% 3.92/0.99  fof(f72,plain,(
% 3.92/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.92/0.99    inference(definition_unfolding,[],[f58,f71])).
% 3.92/0.99  
% 3.92/0.99  fof(f80,plain,(
% 3.92/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.92/0.99    inference(definition_unfolding,[],[f52,f41,f71,f73,f72])).
% 3.92/0.99  
% 3.92/0.99  fof(f27,conjecture,(
% 3.92/0.99    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f28,negated_conjecture,(
% 3.92/0.99    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.92/0.99    inference(negated_conjecture,[],[f27])).
% 3.92/0.99  
% 3.92/0.99  fof(f33,plain,(
% 3.92/0.99    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.92/0.99    inference(ennf_transformation,[],[f28])).
% 3.92/0.99  
% 3.92/0.99  fof(f36,plain,(
% 3.92/0.99    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f37,plain,(
% 3.92/0.99    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 3.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36])).
% 3.92/0.99  
% 3.92/0.99  fof(f66,plain,(
% 3.92/0.99    sK1 != sK3),
% 3.92/0.99    inference(cnf_transformation,[],[f37])).
% 3.92/0.99  
% 3.92/0.99  fof(f16,axiom,(
% 3.92/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f53,plain,(
% 3.92/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f16])).
% 3.92/0.99  
% 3.92/0.99  fof(f8,axiom,(
% 3.92/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f45,plain,(
% 3.92/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f8])).
% 3.92/0.99  
% 3.92/0.99  fof(f67,plain,(
% 3.92/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.92/0.99    inference(definition_unfolding,[],[f45,f41])).
% 3.92/0.99  
% 3.92/0.99  fof(f75,plain,(
% 3.92/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.92/0.99    inference(definition_unfolding,[],[f53,f67,f62,f73])).
% 3.92/0.99  
% 3.92/0.99  fof(f7,axiom,(
% 3.92/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f44,plain,(
% 3.92/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.92/0.99    inference(cnf_transformation,[],[f7])).
% 3.92/0.99  
% 3.92/0.99  fof(f13,axiom,(
% 3.92/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f50,plain,(
% 3.92/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f13])).
% 3.92/0.99  
% 3.92/0.99  fof(f12,axiom,(
% 3.92/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f49,plain,(
% 3.92/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f12])).
% 3.92/0.99  
% 3.92/0.99  fof(f9,axiom,(
% 3.92/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f46,plain,(
% 3.92/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f9])).
% 3.92/0.99  
% 3.92/0.99  fof(f70,plain,(
% 3.92/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.92/0.99    inference(definition_unfolding,[],[f46,f67,f69,f69])).
% 3.92/0.99  
% 3.92/0.99  fof(f74,plain,(
% 3.92/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.92/0.99    inference(definition_unfolding,[],[f49,f67,f73,f70])).
% 3.92/0.99  
% 3.92/0.99  fof(f78,plain,(
% 3.92/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) )),
% 3.92/0.99    inference(definition_unfolding,[],[f50,f67,f68,f69,f74])).
% 3.92/0.99  
% 3.92/0.99  fof(f64,plain,(
% 3.92/0.99    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 3.92/0.99    inference(cnf_transformation,[],[f37])).
% 3.92/0.99  
% 3.92/0.99  fof(f85,plain,(
% 3.92/0.99    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 3.92/0.99    inference(definition_unfolding,[],[f64,f73,f72])).
% 3.92/0.99  
% 3.92/0.99  fof(f5,axiom,(
% 3.92/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f31,plain,(
% 3.92/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.92/0.99    inference(ennf_transformation,[],[f5])).
% 3.92/0.99  
% 3.92/0.99  fof(f42,plain,(
% 3.92/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f31])).
% 3.92/0.99  
% 3.92/0.99  fof(f6,axiom,(
% 3.92/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f43,plain,(
% 3.92/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.92/0.99    inference(cnf_transformation,[],[f6])).
% 3.92/0.99  
% 3.92/0.99  fof(f65,plain,(
% 3.92/0.99    sK1 != sK2),
% 3.92/0.99    inference(cnf_transformation,[],[f37])).
% 3.92/0.99  
% 3.92/0.99  cnf(c_74,plain,
% 3.92/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.92/0.99      theory(equality) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_73,plain,
% 3.92/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.92/0.99      theory(equality) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_92,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3,plain,
% 3.92/0.99      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.92/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2,plain,
% 3.92/0.99      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 3.92/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1,plain,
% 3.92/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.92/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_11,plain,
% 3.92/0.99      ( X0 = X1
% 3.92/0.99      | X2 = X1
% 3.92/0.99      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
% 3.92/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2650,plain,
% 3.92/0.99      ( ~ iProver_ARSWP_43
% 3.92/0.99      | X0 = X1
% 3.92/0.99      | X2 = X1
% 3.92/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0 ),
% 3.92/0.99      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2751,plain,
% 3.92/0.99      ( X0 = X1
% 3.92/0.99      | X2 = X1
% 3.92/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2650]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_16,negated_conjecture,
% 3.92/0.99      ( sK1 != sK3 ),
% 3.92/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2962,plain,
% 3.92/0.99      ( ~ iProver_ARSWP_43
% 3.92/0.99      | X0 = sK3
% 3.92/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.92/0.99      | sK1 = sK3 ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_2650]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2963,plain,
% 3.92/0.99      ( X0 = sK3
% 3.92/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.92/0.99      | sK1 = sK3
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2962]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2965,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.92/0.99      | sK1 = sK3
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_2963]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3080,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top ),
% 3.92/0.99      inference(global_propositional_subsumption,
% 3.92/0.99                [status(thm)],
% 3.92/0.99                [c_2751,c_16,c_2965]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_0,plain,
% 3.92/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.92/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2646,plain,
% 3.92/0.99      ( ~ iProver_ARSWP_39
% 3.92/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0 ),
% 3.92/0.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2755,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2646]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3087,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3080,c_2755]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_6,plain,
% 3.92/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.92/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3091,plain,
% 3.92/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(demodulation,[status(thm)],[c_3087,c_6]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3110,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3091,c_3080]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_9,plain,
% 3.92/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k3_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) ),
% 3.92/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2649,plain,
% 3.92/0.99      ( ~ iProver_ARSWP_42
% 3.92/0.99      | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) ),
% 3.92/0.99      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2752,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2649]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3679,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3080,c_2752]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3711,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.92/0.99      inference(demodulation,[status(thm)],[c_3679,c_6]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3730,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3091,c_3711]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3731,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3711,c_2752]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_6116,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3730,c_3731]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_9953,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3110,c_6116]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3113,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3091,c_2755]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3684,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3091,c_2752]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_6068,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3113,c_3684]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_8381,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3091,c_6068]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_9471,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3080,c_8381]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_8376,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3080,c_6068]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_8431,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(demodulation,[status(thm)],[c_8376,c_6]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_8385,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_6068,c_2752]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_8387,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_6068,c_2755]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_8384,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_6068,c_3711]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_18,negated_conjecture,
% 3.92/0.99      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 3.92/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2652,negated_conjecture,
% 3.92/0.99      ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) | ~ iProver_ARSWP_45 ),
% 3.92/0.99      inference(arg_filter_abstr,[status(unp)],[c_18]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2749,plain,
% 3.92/0.99      ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) = iProver_top
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2652]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_4,plain,
% 3.92/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.92/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2647,plain,
% 3.92/0.99      ( ~ arAF0_r1_tarski_0_1(X0)
% 3.92/0.99      | ~ iProver_ARSWP_40
% 3.92/0.99      | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.92/0.99      inference(arg_filter_abstr,[status(unp)],[c_4]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2754,plain,
% 3.92/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.92/0.99      | arAF0_r1_tarski_0_1(X0) != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2647]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3034,plain,
% 3.92/0.99      ( arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_2749,c_2754]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3086,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3034,c_3080]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3099,plain,
% 3.92/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(demodulation,[status(thm)],[c_3086,c_6]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3228,plain,
% 3.92/0.99      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3099,c_3034]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3728,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3034,c_3711]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5,plain,
% 3.92/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.92/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3771,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(demodulation,[status(thm)],[c_3728,c_5,c_6]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3962,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3099,c_3771]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3683,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3099,c_2752]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5721,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3962,c_3683]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_7096,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_5721,c_3711]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_8089,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_7096]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3232,plain,
% 3.92/0.99      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3099,c_2749]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3405,plain,
% 3.92/0.99      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3232,c_2754]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5726,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3405,c_3683]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5743,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(demodulation,[status(thm)],[c_5726,c_5]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_7095,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_5721,c_5743]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_7390,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3080,c_7095]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_7089,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3080,c_5721]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_7158,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(demodulation,[status(thm)],[c_7089,c_6]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_7092,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3034,c_5721]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_7147,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(demodulation,[status(thm)],[c_7092,c_5,c_6]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_7097,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_5721,c_2752]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5945,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_5743,c_2752]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_6311,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_5945]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3226,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3099,c_3080]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_6308,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3226,c_5945]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_6123,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_3731]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_6070,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3110,c_3684]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3725,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3080,c_3711]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3780,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.92/0.99      inference(demodulation,[status(thm)],[c_3725,c_6]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3909,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3091,c_3780]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_6065,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3909,c_3684]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5727,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_3683]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5724,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0),arAF0_k3_xboole_0_0_1(k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3226,c_3683]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3729,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3099,c_3711]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5177,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_3729]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5719,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)),arAF0_k3_xboole_0_0_1(k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))))) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_5177,c_3683]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5214,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3226,c_5177]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5217,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0))
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_5177]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5531,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_5214,c_5217]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_4982,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3110,c_3909]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_4669,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_3962]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3908,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3099,c_3780]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_4506,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_3908]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_4503,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3226,c_3908]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_4157,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_3226]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3966,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_3771]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3912,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = k1_xboole_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_3780]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3733,plain,
% 3.92/0.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_42 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3711,c_2755]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3412,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_40 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3228,c_3113]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3328,plain,
% 3.92/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3110,c_3113]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3116,plain,
% 3.92/0.99      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.92/0.99      | iProver_ARSWP_45 != iProver_top
% 3.92/0.99      | iProver_ARSWP_43 != iProver_top
% 3.92/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.92/0.99      inference(superposition,[status(thm)],[c_3091,c_2749]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_17,negated_conjecture,
% 3.92/0.99      ( sK1 != sK2 ),
% 3.92/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  % SZS output end Saturation for theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  ------                               Statistics
% 3.92/0.99  
% 3.92/0.99  ------ Selected
% 3.92/0.99  
% 3.92/0.99  total_time:                             0.428
% 3.92/0.99  
%------------------------------------------------------------------------------
