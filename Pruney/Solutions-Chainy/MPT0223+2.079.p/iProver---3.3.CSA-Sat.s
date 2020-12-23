%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:58 EST 2020

% Result     : CounterSatisfiable 7.86s
% Output     : Saturation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  270 (73703 expanded)
%              Number of clauses        :  211 (7702 expanded)
%              Number of leaves         :   23 (23985 expanded)
%              Depth                    :   24
%              Number of atoms          :  864 (97967 expanded)
%              Number of equality atoms :  825 (96092 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    5 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f22,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f23,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

fof(f24,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f24])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f25])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f75,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X0,X0))) = k4_enumset1(X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f55,f42,f72,f76,f75])).

fof(f29,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f29])).

fof(f34,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( sK1 != sK2
    & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f37])).

fof(f68,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f69,f64,f76])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f48,f69,f70,f70])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f46,f69,f70,f64])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))),k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,X8),k3_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,X8),k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3))))))) ),
    inference(definition_unfolding,[],[f54,f69,f74,f76,f71])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k4_enumset1(X1,X1,X1,X2,X3,X4)))),k3_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k4_enumset1(X1,X1,X1,X2,X3,X4)))),k4_enumset1(X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f52,f69,f76,f74,f71])).

fof(f67,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    k3_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f67,f76,f76,f76])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

cnf(c_61,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_60,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_54,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_3,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X0,X2),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X0,X2),k4_enumset1(X1,X1,X1,X1,X1,X1))) = k4_enumset1(X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_988,plain,
    ( ~ iProver_ARSWP_27
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_1079,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
    | iProver_ARSWP_27 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_988])).

cnf(c_18,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1138,plain,
    ( ~ iProver_ARSWP_27
    | X0 = sK2
    | k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_1139,plain,
    ( X0 = sK2
    | k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_27 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_1141,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_27 != iProver_top ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_1466,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
    | iProver_ARSWP_27 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1079,c_18,c_1141])).

cnf(c_0,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_983,plain,
    ( ~ iProver_ARSWP_22
    | k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1084,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_22 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_1477,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0) = arAF0_k4_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1084])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1481,plain,
    ( arAF0_k4_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1477,c_5])).

cnf(c_1532,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1084])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))),k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,X8),k3_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,X8),k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3))))))) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_987,plain,
    ( ~ iProver_ARSWP_26
    | k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_1080,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_987])).

cnf(c_1529,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1080])).

cnf(c_6098,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_1529])).

cnf(c_1475,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1080])).

cnf(c_1488,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1475,c_5])).

cnf(c_1884,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1488])).

cnf(c_1947,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1884,c_5])).

cnf(c_1891,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1080])).

cnf(c_4540,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1947,c_1891])).

cnf(c_27410,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_6098,c_4540])).

cnf(c_27422,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_6098,c_1080])).

cnf(c_31058,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_27422])).

cnf(c_31088,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_27410,c_31058])).

cnf(c_1523,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1466])).

cnf(c_9,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k4_enumset1(X1,X1,X1,X2,X3,X4)))),k3_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k4_enumset1(X1,X1,X1,X2,X3,X4)))),k4_enumset1(X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_985,plain,
    ( ~ iProver_ARSWP_24
    | k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_1082,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_24 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_1473,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1082])).

cnf(c_1504,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1473,c_5])).

cnf(c_2472,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1504])).

cnf(c_2476,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1082])).

cnf(c_15983,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2472,c_2476])).

cnf(c_30149,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_15983])).

cnf(c_11396,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_1504])).

cnf(c_2478,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1080])).

cnf(c_18059,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_2478])).

cnf(c_29419,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_11396,c_18059])).

cnf(c_19,negated_conjecture,
    ( k3_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_989,negated_conjecture,
    ( ~ iProver_ARSWP_28
    | arAF0_k3_xboole_0_0 = arAF0_k4_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_19])).

cnf(c_1078,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_1472,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1466])).

cnf(c_1511,plain,
    ( arAF0_k4_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1472,c_5])).

cnf(c_1275,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1080])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1277,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1275,c_4,c_5])).

cnf(c_1697,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1277])).

cnf(c_1699,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1080])).

cnf(c_8501,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_1699])).

cnf(c_22322,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_8501,c_1080])).

cnf(c_27819,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_22322])).

cnf(c_27423,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_6098,c_1084])).

cnf(c_27418,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_6098,c_1488])).

cnf(c_4545,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1891])).

cnf(c_4556,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4545,c_4])).

cnf(c_27415,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_6098,c_4556])).

cnf(c_4543,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1891])).

cnf(c_21197,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_4543])).

cnf(c_21224,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(demodulation,[status(thm)],[c_21197,c_4])).

cnf(c_27402,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_6098,c_21224])).

cnf(c_1524,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1082])).

cnf(c_4179,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_1524])).

cnf(c_22658,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_4179])).

cnf(c_24620,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_22658])).

cnf(c_2110,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1697])).

cnf(c_8507,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1699])).

cnf(c_9176,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2110,c_8507])).

cnf(c_11390,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_9176])).

cnf(c_9662,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_9176,c_1080])).

cnf(c_15622,plain,
    ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_9662])).

cnf(c_24018,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_11390,c_15622])).

cnf(c_22656,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_4179])).

cnf(c_22728,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(demodulation,[status(thm)],[c_22656,c_5])).

cnf(c_22676,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_4179,c_1082])).

cnf(c_22679,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_4179,c_1084])).

cnf(c_22673,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_4179,c_1504])).

cnf(c_22321,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_8501,c_1277])).

cnf(c_22318,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_8501,c_1488])).

cnf(c_4544,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1891])).

cnf(c_4565,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4544,c_4])).

cnf(c_22314,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_8501,c_4565])).

cnf(c_6955,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_4565])).

cnf(c_7013,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6955,c_5])).

cnf(c_8818,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_7013])).

cnf(c_9171,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_8818,c_8507])).

cnf(c_22313,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_8501,c_9171])).

cnf(c_22312,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_8501,c_9176])).

cnf(c_9183,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_8507])).

cnf(c_9189,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_9183,c_4])).

cnf(c_22311,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_8501,c_9189])).

cnf(c_22310,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_8501,c_4540])).

cnf(c_1693,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1466])).

cnf(c_1962,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1693])).

cnf(c_1694,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1082])).

cnf(c_5424,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1694])).

cnf(c_5752,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_5424])).

cnf(c_21199,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_5752])).

cnf(c_21728,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_21199])).

cnf(c_21722,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_9176,c_21199])).

cnf(c_21720,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_21199])).

cnf(c_2470,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1504])).

cnf(c_2552,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2470,c_5])).

cnf(c_2702,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_2552])).

cnf(c_3583,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_2702])).

cnf(c_5747,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_3583,c_5424])).

cnf(c_5833,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5747,c_1082])).

cnf(c_13150,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_5833])).

cnf(c_14281,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_13150])).

cnf(c_21198,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_14281])).

cnf(c_21426,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_21198])).

cnf(c_21425,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5747,c_21198])).

cnf(c_21420,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_9176,c_21198])).

cnf(c_21422,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_4565,c_21198])).

cnf(c_21418,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_21198])).

cnf(c_1377,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1082])).

cnf(c_1379,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1377,c_4,c_5])).

cnf(c_1754,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1379])).

cnf(c_5420,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_1694])).

cnf(c_14276,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_3583,c_13150])).

cnf(c_20324,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5420,c_14276])).

cnf(c_15993,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_2476])).

cnf(c_20607,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_20324,c_15993])).

cnf(c_20335,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5420,c_1082])).

cnf(c_20334,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5420,c_1379])).

cnf(c_20332,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5420,c_1504])).

cnf(c_20331,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5420,c_5747])).

cnf(c_5755,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_5424])).

cnf(c_5761,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5755,c_4])).

cnf(c_5762,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5761,c_4])).

cnf(c_20330,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5420,c_5762])).

cnf(c_2471,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1504])).

cnf(c_5179,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_2471])).

cnf(c_17196,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_15993])).

cnf(c_17264,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k1_xboole_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_17196])).

cnf(c_17281,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_17264,c_4])).

cnf(c_18120,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_17281])).

cnf(c_20323,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5420,c_18120])).

cnf(c_5418,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2702,c_1694])).

cnf(c_20322,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5420,c_5418])).

cnf(c_6964,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4565,c_1080])).

cnf(c_19853,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_6964])).

cnf(c_6462,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_4556,c_1080])).

cnf(c_19728,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_6462])).

cnf(c_18973,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_18120])).

cnf(c_18985,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_18120,c_1504])).

cnf(c_18976,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_18120,c_14276])).

cnf(c_18124,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_17281])).

cnf(c_17189,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_11390,c_15993])).

cnf(c_15987,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2471,c_2476])).

cnf(c_9585,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_9171,c_1080])).

cnf(c_15565,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_9585])).

cnf(c_14785,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_14276,c_1082])).

cnf(c_14782,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_14276,c_1504])).

cnf(c_13147,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_5833])).

cnf(c_11385,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_4540])).

cnf(c_11515,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_11385,c_5])).

cnf(c_11401,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_1080])).

cnf(c_11399,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_1082])).

cnf(c_11402,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_1084])).

cnf(c_11400,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_1277])).

cnf(c_11397,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_1488])).

cnf(c_11393,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_4556])).

cnf(c_11392,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_4565])).

cnf(c_11391,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_9171])).

cnf(c_1886,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1488])).

cnf(c_11008,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_1529])).

cnf(c_9577,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_9171,c_4565])).

cnf(c_10635,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_9577,c_1699])).

cnf(c_9648,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_9176])).

cnf(c_9743,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_9648,c_5])).

cnf(c_9661,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_9176,c_1277])).

cnf(c_9658,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_9176,c_1488])).

cnf(c_9653,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_9176,c_4565])).

cnf(c_9652,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_9176,c_9171])).

cnf(c_1885,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1488])).

cnf(c_8497,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_1699])).

cnf(c_5830,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5747,c_1504])).

cnf(c_8219,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_5830])).

cnf(c_5827,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_5747])).

cnf(c_8157,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_5827,c_1694])).

cnf(c_8154,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_5827])).

cnf(c_6453,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_4556])).

cnf(c_6524,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6453,c_5])).

cnf(c_5423,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_1694])).

cnf(c_2703,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_2552])).

cnf(c_4507,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2703,c_1524])).

cnf(c_4504,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_2703])).

cnf(c_4182,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_1524])).

cnf(c_3832,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1885])).

cnf(c_3582,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_2702])).

cnf(c_2475,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1379])).

cnf(c_3328,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_2475])).

cnf(c_2899,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1532])).

cnf(c_2897,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = arAF0_k4_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_1532])).

cnf(c_2705,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_2552])).

cnf(c_2479,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1084])).

cnf(c_2474,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1488])).

cnf(c_2276,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = arAF0_k4_enumset1_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1754])).

cnf(c_1889,plain,
    ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1082])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:23:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.86/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/1.47  
% 7.86/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.86/1.47  
% 7.86/1.47  ------  iProver source info
% 7.86/1.47  
% 7.86/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.86/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.86/1.47  git: non_committed_changes: false
% 7.86/1.47  git: last_make_outside_of_git: false
% 7.86/1.47  
% 7.86/1.47  ------ 
% 7.86/1.47  ------ Parsing...
% 7.86/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.86/1.47  ------ Proving...
% 7.86/1.47  ------ Problem Properties 
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  clauses                                 17
% 7.86/1.47  conjectures                             2
% 7.86/1.47  EPR                                     1
% 7.86/1.47  Horn                                    16
% 7.86/1.47  unary                                   16
% 7.86/1.47  binary                                  0
% 7.86/1.47  lits                                    19
% 7.86/1.47  lits eq                                 19
% 7.86/1.47  fd_pure                                 0
% 7.86/1.47  fd_pseudo                               0
% 7.86/1.47  fd_cond                                 0
% 7.86/1.47  fd_pseudo_cond                          1
% 7.86/1.47  AC symbols                              0
% 7.86/1.47  
% 7.86/1.47  ------ Input Options Time Limit: Unbounded
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 7.86/1.47  Current options:
% 7.86/1.47  ------ 
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  ------ Proving...
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.86/1.47  
% 7.86/1.47  ------ Proving...
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.86/1.47  
% 7.86/1.47  ------ Proving...
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.86/1.47  
% 7.86/1.47  ------ Proving...
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.86/1.47  
% 7.86/1.47  ------ Proving...
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.86/1.47  
% 7.86/1.47  ------ Proving...
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.86/1.47  
% 7.86/1.47  ------ Proving...
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  % SZS status CounterSatisfiable for theBenchmark.p
% 7.86/1.47  
% 7.86/1.47  % SZS output start Saturation for theBenchmark.p
% 7.86/1.47  
% 7.86/1.47  fof(f3,axiom,(
% 7.86/1.47    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f41,plain,(
% 7.86/1.47    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 7.86/1.47    inference(cnf_transformation,[],[f3])).
% 7.86/1.47  
% 7.86/1.47  fof(f2,axiom,(
% 7.86/1.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f31,plain,(
% 7.86/1.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.86/1.47    inference(rectify,[],[f2])).
% 7.86/1.47  
% 7.86/1.47  fof(f32,plain,(
% 7.86/1.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.86/1.47    inference(ennf_transformation,[],[f31])).
% 7.86/1.47  
% 7.86/1.47  fof(f35,plain,(
% 7.86/1.47    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.86/1.47    introduced(choice_axiom,[])).
% 7.86/1.47  
% 7.86/1.47  fof(f36,plain,(
% 7.86/1.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.86/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f35])).
% 7.86/1.47  
% 7.86/1.47  fof(f39,plain,(
% 7.86/1.47    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f36])).
% 7.86/1.47  
% 7.86/1.47  fof(f40,plain,(
% 7.86/1.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.86/1.47    inference(cnf_transformation,[],[f36])).
% 7.86/1.47  
% 7.86/1.47  fof(f17,axiom,(
% 7.86/1.47    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f33,plain,(
% 7.86/1.47    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 7.86/1.47    inference(ennf_transformation,[],[f17])).
% 7.86/1.47  
% 7.86/1.47  fof(f55,plain,(
% 7.86/1.47    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f4,axiom,(
% 7.86/1.47    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f42,plain,(
% 7.86/1.47    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f4])).
% 7.86/1.47  
% 7.86/1.47  fof(f22,axiom,(
% 7.86/1.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f60,plain,(
% 7.86/1.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f22])).
% 7.86/1.47  
% 7.86/1.47  fof(f76,plain,(
% 7.86/1.47    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 7.86/1.47    inference(definition_unfolding,[],[f60,f75])).
% 7.86/1.47  
% 7.86/1.47  fof(f23,axiom,(
% 7.86/1.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f61,plain,(
% 7.86/1.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f23])).
% 7.86/1.47  
% 7.86/1.47  fof(f24,axiom,(
% 7.86/1.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f62,plain,(
% 7.86/1.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f24])).
% 7.86/1.47  
% 7.86/1.47  fof(f25,axiom,(
% 7.86/1.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f63,plain,(
% 7.86/1.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f25])).
% 7.86/1.47  
% 7.86/1.47  fof(f26,axiom,(
% 7.86/1.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f64,plain,(
% 7.86/1.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f26])).
% 7.86/1.47  
% 7.86/1.47  fof(f70,plain,(
% 7.86/1.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.86/1.47    inference(definition_unfolding,[],[f63,f64])).
% 7.86/1.47  
% 7.86/1.47  fof(f72,plain,(
% 7.86/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 7.86/1.47    inference(definition_unfolding,[],[f62,f70])).
% 7.86/1.47  
% 7.86/1.47  fof(f75,plain,(
% 7.86/1.47    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.86/1.47    inference(definition_unfolding,[],[f61,f72])).
% 7.86/1.47  
% 7.86/1.47  fof(f84,plain,(
% 7.86/1.47    ( ! [X2,X0,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X0,X0))) = k4_enumset1(X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 7.86/1.47    inference(definition_unfolding,[],[f55,f42,f72,f76,f75])).
% 7.86/1.47  
% 7.86/1.47  fof(f29,conjecture,(
% 7.86/1.47    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f30,negated_conjecture,(
% 7.86/1.47    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.86/1.47    inference(negated_conjecture,[],[f29])).
% 7.86/1.47  
% 7.86/1.47  fof(f34,plain,(
% 7.86/1.47    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 7.86/1.47    inference(ennf_transformation,[],[f30])).
% 7.86/1.47  
% 7.86/1.47  fof(f37,plain,(
% 7.86/1.47    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 7.86/1.47    introduced(choice_axiom,[])).
% 7.86/1.47  
% 7.86/1.47  fof(f38,plain,(
% 7.86/1.47    sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 7.86/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f37])).
% 7.86/1.47  
% 7.86/1.47  fof(f68,plain,(
% 7.86/1.47    sK1 != sK2),
% 7.86/1.47    inference(cnf_transformation,[],[f38])).
% 7.86/1.47  
% 7.86/1.47  fof(f18,axiom,(
% 7.86/1.47    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f56,plain,(
% 7.86/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f18])).
% 7.86/1.47  
% 7.86/1.47  fof(f7,axiom,(
% 7.86/1.47    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f45,plain,(
% 7.86/1.47    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f7])).
% 7.86/1.47  
% 7.86/1.47  fof(f69,plain,(
% 7.86/1.47    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.86/1.47    inference(definition_unfolding,[],[f45,f42])).
% 7.86/1.47  
% 7.86/1.47  fof(f77,plain,(
% 7.86/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.86/1.47    inference(definition_unfolding,[],[f56,f69,f64,f76])).
% 7.86/1.47  
% 7.86/1.47  fof(f6,axiom,(
% 7.86/1.47    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f44,plain,(
% 7.86/1.47    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.86/1.47    inference(cnf_transformation,[],[f6])).
% 7.86/1.47  
% 7.86/1.47  fof(f16,axiom,(
% 7.86/1.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f54,plain,(
% 7.86/1.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f16])).
% 7.86/1.47  
% 7.86/1.47  fof(f10,axiom,(
% 7.86/1.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f48,plain,(
% 7.86/1.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f10])).
% 7.86/1.47  
% 7.86/1.47  fof(f74,plain,(
% 7.86/1.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.86/1.47    inference(definition_unfolding,[],[f48,f69,f70,f70])).
% 7.86/1.47  
% 7.86/1.47  fof(f8,axiom,(
% 7.86/1.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f46,plain,(
% 7.86/1.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f8])).
% 7.86/1.47  
% 7.86/1.47  fof(f71,plain,(
% 7.86/1.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.86/1.47    inference(definition_unfolding,[],[f46,f69,f70,f64])).
% 7.86/1.47  
% 7.86/1.47  fof(f83,plain,(
% 7.86/1.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))),k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,X8),k3_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,X8),k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))))))) )),
% 7.86/1.47    inference(definition_unfolding,[],[f54,f69,f74,f76,f71])).
% 7.86/1.47  
% 7.86/1.47  fof(f14,axiom,(
% 7.86/1.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f52,plain,(
% 7.86/1.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f14])).
% 7.86/1.47  
% 7.86/1.47  fof(f81,plain,(
% 7.86/1.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3)))) = k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k4_enumset1(X1,X1,X1,X2,X3,X4)))),k3_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k4_enumset1(X1,X1,X1,X2,X3,X4)))),k4_enumset1(X0,X0,X0,X0,X0,X0))))) )),
% 7.86/1.47    inference(definition_unfolding,[],[f52,f69,f76,f74,f71])).
% 7.86/1.47  
% 7.86/1.47  fof(f67,plain,(
% 7.86/1.47    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 7.86/1.47    inference(cnf_transformation,[],[f38])).
% 7.86/1.47  
% 7.86/1.47  fof(f90,plain,(
% 7.86/1.47    k3_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),
% 7.86/1.47    inference(definition_unfolding,[],[f67,f76,f76,f76])).
% 7.86/1.47  
% 7.86/1.47  fof(f5,axiom,(
% 7.86/1.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f43,plain,(
% 7.86/1.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.86/1.47    inference(cnf_transformation,[],[f5])).
% 7.86/1.47  
% 7.86/1.47  cnf(c_61,plain,
% 7.86/1.47      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.86/1.47      theory(equality) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_60,plain,
% 7.86/1.47      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.86/1.47      theory(equality) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_54,plain,( X0_2 = X0_2 ),theory(equality) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3,plain,
% 7.86/1.47      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 7.86/1.47      inference(cnf_transformation,[],[f41]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2,plain,
% 7.86/1.47      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 7.86/1.47      inference(cnf_transformation,[],[f39]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1,plain,
% 7.86/1.47      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.86/1.47      inference(cnf_transformation,[],[f40]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_12,plain,
% 7.86/1.47      ( X0 = X1
% 7.86/1.47      | X2 = X1
% 7.86/1.47      | k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X0,X2),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X0,X2),k4_enumset1(X1,X1,X1,X1,X1,X1))) = k4_enumset1(X0,X0,X0,X0,X0,X2) ),
% 7.86/1.47      inference(cnf_transformation,[],[f84]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_988,plain,
% 7.86/1.47      ( ~ iProver_ARSWP_27
% 7.86/1.47      | X0 = X1
% 7.86/1.47      | X2 = X1
% 7.86/1.47      | k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0 ),
% 7.86/1.47      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1079,plain,
% 7.86/1.47      ( X0 = X1
% 7.86/1.47      | X2 = X1
% 7.86/1.47      | k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_988]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_18,negated_conjecture,
% 7.86/1.47      ( sK1 != sK2 ),
% 7.86/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1138,plain,
% 7.86/1.47      ( ~ iProver_ARSWP_27
% 7.86/1.47      | X0 = sK2
% 7.86/1.47      | k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
% 7.86/1.47      | sK1 = sK2 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_988]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1139,plain,
% 7.86/1.47      ( X0 = sK2
% 7.86/1.47      | k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
% 7.86/1.47      | sK1 = sK2
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1141,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
% 7.86/1.47      | sK1 = sK2
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1139]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1466,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_1079,c_18,c_1141]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_0,plain,
% 7.86/1.47      ( k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 7.86/1.47      inference(cnf_transformation,[],[f77]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_983,plain,
% 7.86/1.47      ( ~ iProver_ARSWP_22
% 7.86/1.47      | k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0 ),
% 7.86/1.47      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1084,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1477,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_1084]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5,plain,
% 7.86/1.47      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.86/1.47      inference(cnf_transformation,[],[f44]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1481,plain,
% 7.86/1.47      ( arAF0_k4_enumset1_0 = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_1477,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1532,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1481,c_1084]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3)))),k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,X8),k3_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,X8),k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k3_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k4_enumset1(X0,X0,X0,X1,X2,X3))))))) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
% 7.86/1.47      inference(cnf_transformation,[],[f83]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_987,plain,
% 7.86/1.47      ( ~ iProver_ARSWP_26
% 7.86/1.47      | k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) ),
% 7.86/1.47      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1080,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_987]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1529,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1481,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_6098,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1532,c_1529]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1475,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1488,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_1475,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1884,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_1488]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1947,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_1884,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1891,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1488,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4540,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1947,c_1891]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_27410,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_6098,c_4540]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_27422,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_6098,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_31058,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_27422]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_31088,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_27410,c_31058]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1523,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1481,c_1466]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9,plain,
% 7.86/1.47      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k4_enumset1(X1,X1,X1,X2,X3,X4)))),k3_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X5,X5,X5,X6,X7,X8),k4_enumset1(X1,X1,X1,X2,X3,X4)))),k4_enumset1(X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X4,X4,X5,X6,X7,X8),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
% 7.86/1.47      inference(cnf_transformation,[],[f81]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_985,plain,
% 7.86/1.47      ( ~ iProver_ARSWP_24
% 7.86/1.47      | k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) ),
% 7.86/1.47      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1082,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1473,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_1082]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1504,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_1473,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2472,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1481,c_1504]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2476,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1504,c_1082]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_15983,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_2472,c_2476]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_30149,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1523,c_15983]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11396,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_1504]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2478,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1504,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_18059,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_2478]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_29419,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_11396,c_18059]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_19,negated_conjecture,
% 7.86/1.47      ( k3_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
% 7.86/1.47      inference(cnf_transformation,[],[f90]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_989,negated_conjecture,
% 7.86/1.47      ( ~ iProver_ARSWP_28 | arAF0_k3_xboole_0_0 = arAF0_k4_enumset1_0 ),
% 7.86/1.47      inference(arg_filter_abstr,[status(unp)],[c_19]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1078,plain,
% 7.86/1.47      ( arAF0_k3_xboole_0_0 = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_989]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1472,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_1466]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1511,plain,
% 7.86/1.47      ( arAF0_k4_enumset1_0 = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_1472,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1275,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4,plain,
% 7.86/1.47      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.86/1.47      inference(cnf_transformation,[],[f43]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1277,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_1275,c_4,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1697,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_1277]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1699,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_8501,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1697,c_1699]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22322,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_8501,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_27819,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_22322]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_27423,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_6098,c_1084]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_27418,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_6098,c_1488]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4545,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1481,c_1891]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4556,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_4545,c_4]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_27415,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_6098,c_4556]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4543,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_1891]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21197,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1481,c_4543]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21224,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_21197,c_4]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_27402,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_6098,c_21224]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1524,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1481,c_1082]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4179,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1532,c_1524]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22658,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1481,c_4179]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_24620,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_22658]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2110,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_1697]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_8507,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_1699]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9176,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_2110,c_8507]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11390,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_9176]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9662,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_9176,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_15622,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_9662]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_24018,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_11390,c_15622]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22656,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_4179]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22728,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_22656,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22676,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4179,c_1082]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22679,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4179,c_1084]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22673,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4179,c_1504]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22321,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_8501,c_1277]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22318,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_8501,c_1488]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4544,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_1891]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4565,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_4544,c_4]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22314,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_8501,c_4565]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_6955,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_4565]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_7013,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_6955,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_8818,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_7013]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9171,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_8818,c_8507]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22313,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_8501,c_9171]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22312,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_8501,c_9176]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9183,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_8507]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9189,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_9183,c_4]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22311,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_8501,c_9189]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22310,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_8501,c_4540]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1693,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_1466]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1962,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_1693]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1694,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_1082]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5424,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_1694]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5752,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1962,c_5424]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21199,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4543,c_5752]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21728,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1504,c_21199]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21722,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_9176,c_21199]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21720,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_21199]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2470,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_1504]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2552,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_2470,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2702,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_2552]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3583,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_2702]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5747,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_3583,c_5424]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5833,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5747,c_1082]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_13150,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_5833]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_14281,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1962,c_13150]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21198,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4543,c_14281]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21426,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1504,c_21198]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21425,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5747,c_21198]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21420,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_9176,c_21198]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21422,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4565,c_21198]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21418,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_21198]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1377,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_1082]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1379,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_1377,c_4,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1754,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_1379]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5420,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1754,c_1694]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_14276,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_3583,c_13150]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_20324,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5420,c_14276]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_15993,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_2476]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_20607,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_20324,c_15993]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_20335,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5420,c_1082]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_20334,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5420,c_1379]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_20332,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5420,c_1504]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_20331,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5420,c_5747]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5755,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_5424]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5761,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_5755,c_4]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5762,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_5761,c_4]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_20330,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5420,c_5762]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2471,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_1504]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5179,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_2471]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_17196,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5179,c_15993]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_17264,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k1_xboole_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_17196]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_17281,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_17264,c_4]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_18120,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1754,c_17281]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_20323,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5420,c_18120]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5418,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_2702,c_1694]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_20322,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5420,c_5418]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_6964,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4565,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_19853,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_6964]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_6462,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4556,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_19728,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_6462]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_18973,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_18120]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_18985,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_18120,c_1504]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_18976,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_18120,c_14276]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_18124,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_17281]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_17189,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_11390,c_15993]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_15987,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_2471,c_2476]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9585,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_9171,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_15565,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k4_enumset1_0) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_9585]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_14785,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_14276,c_1082]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_14782,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_14276,c_1504]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_13147,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1962,c_5833]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11385,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_4540]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11515,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_11385,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11401,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_1080]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11399,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_1082]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11402,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_1084]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11400,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_1277]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11397,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_1488]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11393,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_4556]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11392,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_4565]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11391,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_4540,c_9171]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1886,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1481,c_1488]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11008,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1886,c_1529]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9577,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_9171,c_4565]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_10635,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_9577,c_1699]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9648,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_9176]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9743,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_9648,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9661,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_9176,c_1277]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9658,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_9176,c_1488]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9653,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_9176,c_4565]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9652,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_9176,c_9171]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1885,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_1488]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_8497,plain,
% 7.86/1.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1885,c_1699]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5830,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5747,c_1504]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_8219,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_5830]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5827,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1511,c_5747]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_8157,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_5827,c_1694]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_8154,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1693,c_5827]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_6453,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1466,c_4556]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_6524,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_6453,c_5]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5423,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1693,c_1694]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2703,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1481,c_2552]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4507,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_2703,c_1524]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4504,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1523,c_2703]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4182,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top
% 7.86/1.47      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1523,c_1524]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3832,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_26 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_1885]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3582,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = k1_xboole_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1693,c_2702]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2475,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1504,c_1379]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3328,plain,
% 7.86/1.47      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.47      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1078,c_2475]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2899,plain,
% 7.86/1.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = arAF0_k4_enumset1_0
% 7.86/1.47      | iProver_ARSWP_28 != iProver_top
% 7.86/1.47      | iProver_ARSWP_27 != iProver_top
% 7.86/1.48      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.48      inference(superposition,[status(thm)],[c_1078,c_1532]) ).
% 7.86/1.48  
% 7.86/1.48  cnf(c_2897,plain,
% 7.86/1.48      ( k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0) = arAF0_k4_enumset1_0
% 7.86/1.48      | iProver_ARSWP_27 != iProver_top
% 7.86/1.48      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.48      inference(superposition,[status(thm)],[c_1523,c_1532]) ).
% 7.86/1.48  
% 7.86/1.48  cnf(c_2705,plain,
% 7.86/1.48      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = k1_xboole_0
% 7.86/1.48      | iProver_ARSWP_28 != iProver_top
% 7.86/1.48      | iProver_ARSWP_27 != iProver_top
% 7.86/1.48      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.48      inference(superposition,[status(thm)],[c_1078,c_2552]) ).
% 7.86/1.48  
% 7.86/1.48  cnf(c_2479,plain,
% 7.86/1.48      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k4_enumset1_0
% 7.86/1.48      | iProver_ARSWP_27 != iProver_top
% 7.86/1.48      | iProver_ARSWP_24 != iProver_top
% 7.86/1.48      | iProver_ARSWP_22 != iProver_top ),
% 7.86/1.48      inference(superposition,[status(thm)],[c_1504,c_1084]) ).
% 7.86/1.48  
% 7.86/1.48  cnf(c_2474,plain,
% 7.86/1.48      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)
% 7.86/1.48      | iProver_ARSWP_27 != iProver_top
% 7.86/1.48      | iProver_ARSWP_26 != iProver_top
% 7.86/1.48      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.48      inference(superposition,[status(thm)],[c_1504,c_1488]) ).
% 7.86/1.48  
% 7.86/1.48  cnf(c_2276,plain,
% 7.86/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0)) = arAF0_k4_enumset1_0
% 7.86/1.48      | iProver_ARSWP_28 != iProver_top
% 7.86/1.48      | iProver_ARSWP_27 != iProver_top
% 7.86/1.48      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.48      inference(superposition,[status(thm)],[c_1078,c_1754]) ).
% 7.86/1.48  
% 7.86/1.48  cnf(c_1889,plain,
% 7.86/1.48      ( k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,arAF0_k4_enumset1_0),arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k4_enumset1_0,k5_xboole_0(arAF0_k4_enumset1_0,arAF0_k3_xboole_0_0))
% 7.86/1.48      | iProver_ARSWP_27 != iProver_top
% 7.86/1.48      | iProver_ARSWP_26 != iProver_top
% 7.86/1.48      | iProver_ARSWP_24 != iProver_top ),
% 7.86/1.48      inference(superposition,[status(thm)],[c_1488,c_1082]) ).
% 7.86/1.48  
% 7.86/1.48  
% 7.86/1.48  % SZS output end Saturation for theBenchmark.p
% 7.86/1.48  
% 7.86/1.48  ------                               Statistics
% 7.86/1.48  
% 7.86/1.48  ------ Selected
% 7.86/1.48  
% 7.86/1.48  total_time:                             0.878
% 7.86/1.48  
%------------------------------------------------------------------------------
