%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:44 EST 2020

% Result     : CounterSatisfiable 3.64s
% Output     : Saturation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 273 expanded)
%              Number of clauses        :   57 (  88 expanded)
%              Number of leaves         :   21 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  250 ( 468 expanded)
%              Number of equality atoms :  194 ( 391 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f44,f48])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k2_tarski(X0,X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f45,f60,f48])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f27,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f32])).

fof(f59,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f55,f48,f48])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f44,f48,f60])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f61,f63])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f56,f48])).

fof(f79,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f72])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

cnf(c_89,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_10,plain,
    ( X0 = X1
    | X2 = X1
    | k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))),k2_tarski(X1,X1)) = k2_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5493,plain,
    ( ~ iProver_ARSWP_96
    | X0 = X1
    | X2 = X1
    | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_5629,plain,
    ( X0 = X1
    | X2 = X1
    | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
    | iProver_ARSWP_96 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5493])).

cnf(c_16,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_140,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_614,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_1738,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_1946,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_1947,plain,
    ( X0 != sK1
    | sK1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1946])).

cnf(c_5754,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_5770,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_5754])).

cnf(c_5771,plain,
    ( X0 != sK0
    | sK0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5770])).

cnf(c_5777,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) != sK0
    | sK0 = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5771])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5783,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5746,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_5803,plain,
    ( sK1 != k5_xboole_0(sK0,k1_xboole_0)
    | sK0 != k5_xboole_0(sK0,k1_xboole_0)
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_5746])).

cnf(c_5804,plain,
    ( X0 != k5_xboole_0(sK0,k1_xboole_0)
    | sK0 = X0
    | sK0 != k5_xboole_0(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5754])).

cnf(c_6017,plain,
    ( ~ iProver_ARSWP_96
    | X0 = sK1
    | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_5493])).

cnf(c_6018,plain,
    ( X0 = sK1
    | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
    | sK0 = sK1
    | iProver_ARSWP_96 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6017])).

cnf(c_6042,plain,
    ( ~ iProver_ARSWP_96
    | X0 = k5_xboole_0(sK0,k1_xboole_0)
    | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
    | sK1 = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5493])).

cnf(c_6043,plain,
    ( X0 = k5_xboole_0(sK0,k1_xboole_0)
    | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
    | sK1 = k5_xboole_0(sK0,k1_xboole_0)
    | iProver_ARSWP_96 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6042])).

cnf(c_6588,plain,
    ( k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
    | iProver_ARSWP_96 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5629,c_16,c_614,c_1947,c_5777,c_5783,c_5803,c_5804,c_6018,c_6043])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5910,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5911,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_5921,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5911,c_7])).

cnf(c_5913,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_5915,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5913,c_6])).

cnf(c_5922,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5921,c_5915])).

cnf(c_5926,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5910,c_5922])).

cnf(c_6592,plain,
    ( arAF0_k2_tarski_0 = k1_xboole_0
    | iProver_ARSWP_96 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6588,c_7,c_5926])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X1))
    | k2_tarski(X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5498,plain,
    ( ~ r1_tarski(X0,arAF0_k2_tarski_0)
    | ~ iProver_ARSWP_101
    | arAF0_k2_tarski_0 = X0
    | k1_xboole_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_15])).

cnf(c_5624,plain,
    ( arAF0_k2_tarski_0 = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,arAF0_k2_tarski_0) != iProver_top
    | iProver_ARSWP_101 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5498])).

cnf(c_6597,plain,
    ( arAF0_k2_tarski_0 = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | iProver_ARSWP_101 != iProver_top
    | iProver_ARSWP_96 != iProver_top ),
    inference(superposition,[status(thm)],[c_6592,c_5624])).

cnf(c_12,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5495,plain,
    ( ~ iProver_ARSWP_98
    | k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_5627,plain,
    ( k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_98 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5495])).

cnf(c_6391,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k2_tarski_0
    | iProver_ARSWP_98 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5627,c_7,c_5926])).

cnf(c_14,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_5497,plain,
    ( r1_tarski(k1_xboole_0,arAF0_k2_tarski_0)
    | ~ iProver_ARSWP_100 ),
    inference(arg_filter_abstr,[status(unp)],[c_14])).

cnf(c_5625,plain,
    ( r1_tarski(k1_xboole_0,arAF0_k2_tarski_0) = iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5497])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5635,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6148,plain,
    ( arAF0_k2_tarski_0 = k1_xboole_0
    | r1_tarski(arAF0_k2_tarski_0,k1_xboole_0) != iProver_top
    | iProver_ARSWP_100 != iProver_top ),
    inference(superposition,[status(thm)],[c_5625,c_5635])).

cnf(c_9,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5492,plain,
    ( arAF0_r1_xboole_0_0_1(k1_xboole_0)
    | ~ iProver_ARSWP_95 ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_5630,plain,
    ( arAF0_r1_xboole_0_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_95 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5492])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5491,plain,
    ( ~ arAF0_r1_xboole_0_0_1(X0)
    | ~ iProver_ARSWP_94
    | k1_xboole_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_5631,plain,
    ( k1_xboole_0 = X0
    | arAF0_r1_xboole_0_0_1(X0) != iProver_top
    | iProver_ARSWP_94 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5491])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5634,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.64/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/1.00  
% 3.64/1.00  ------  iProver source info
% 3.64/1.00  
% 3.64/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.64/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/1.00  git: non_committed_changes: false
% 3.64/1.00  git: last_make_outside_of_git: false
% 3.64/1.00  
% 3.64/1.00  ------ 
% 3.64/1.00  ------ Parsing...
% 3.64/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  ------ Proving...
% 3.64/1.00  ------ Problem Properties 
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  clauses                                 17
% 3.64/1.00  conjectures                             2
% 3.64/1.00  EPR                                     5
% 3.64/1.00  Horn                                    15
% 3.64/1.00  unary                                   13
% 3.64/1.00  binary                                  1
% 3.64/1.00  lits                                    24
% 3.64/1.00  lits eq                                 15
% 3.64/1.00  fd_pure                                 0
% 3.64/1.00  fd_pseudo                               0
% 3.64/1.00  fd_cond                                 1
% 3.64/1.00  fd_pseudo_cond                          3
% 3.64/1.00  AC symbols                              0
% 3.64/1.00  
% 3.64/1.00  ------ Input Options Time Limit: Unbounded
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.64/1.00  Current options:
% 3.64/1.00  ------ 
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  % SZS output start Saturation for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  fof(f10,axiom,(
% 3.64/1.00    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f26,plain,(
% 3.64/1.00    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.64/1.00    inference(ennf_transformation,[],[f10])).
% 3.64/1.00  
% 3.64/1.00  fof(f45,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.64/1.00    inference(cnf_transformation,[],[f26])).
% 3.64/1.00  
% 3.64/1.00  fof(f11,axiom,(
% 3.64/1.00    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f46,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f11])).
% 3.64/1.00  
% 3.64/1.00  fof(f9,axiom,(
% 3.64/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f44,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f9])).
% 3.64/1.00  
% 3.64/1.00  fof(f60,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k1_enumset1(X0,X1,X2)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f46,f44,f48])).
% 3.64/1.00  
% 3.64/1.00  fof(f13,axiom,(
% 3.64/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f48,plain,(
% 3.64/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f13])).
% 3.64/1.00  
% 3.64/1.00  fof(f68,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k2_tarski(X0,X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.64/1.00    inference(definition_unfolding,[],[f45,f60,f48])).
% 3.64/1.00  
% 3.64/1.00  fof(f21,conjecture,(
% 3.64/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f22,negated_conjecture,(
% 3.64/1.00    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.64/1.00    inference(negated_conjecture,[],[f21])).
% 3.64/1.00  
% 3.64/1.00  fof(f27,plain,(
% 3.64/1.00    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.64/1.00    inference(ennf_transformation,[],[f22])).
% 3.64/1.00  
% 3.64/1.00  fof(f32,plain,(
% 3.64/1.00    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 3.64/1.00    introduced(choice_axiom,[])).
% 3.64/1.00  
% 3.64/1.00  fof(f33,plain,(
% 3.64/1.00    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 3.64/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f32])).
% 3.64/1.00  
% 3.64/1.00  fof(f59,plain,(
% 3.64/1.00    sK0 != sK1),
% 3.64/1.00    inference(cnf_transformation,[],[f33])).
% 3.64/1.00  
% 3.64/1.00  fof(f6,axiom,(
% 3.64/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f41,plain,(
% 3.64/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.64/1.00    inference(cnf_transformation,[],[f6])).
% 3.64/1.00  
% 3.64/1.00  fof(f1,axiom,(
% 3.64/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f23,plain,(
% 3.64/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.64/1.00    inference(rectify,[],[f1])).
% 3.64/1.00  
% 3.64/1.00  fof(f34,plain,(
% 3.64/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.64/1.00    inference(cnf_transformation,[],[f23])).
% 3.64/1.00  
% 3.64/1.00  fof(f5,axiom,(
% 3.64/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f40,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.64/1.00    inference(cnf_transformation,[],[f5])).
% 3.64/1.00  
% 3.64/1.00  fof(f66,plain,(
% 3.64/1.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.64/1.00    inference(definition_unfolding,[],[f34,f40])).
% 3.64/1.00  
% 3.64/1.00  fof(f3,axiom,(
% 3.64/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f38,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.64/1.00    inference(cnf_transformation,[],[f3])).
% 3.64/1.00  
% 3.64/1.00  fof(f64,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.64/1.00    inference(definition_unfolding,[],[f38,f40])).
% 3.64/1.00  
% 3.64/1.00  fof(f4,axiom,(
% 3.64/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f39,plain,(
% 3.64/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.64/1.00    inference(cnf_transformation,[],[f4])).
% 3.64/1.00  
% 3.64/1.00  fof(f67,plain,(
% 3.64/1.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.64/1.00    inference(definition_unfolding,[],[f39,f40])).
% 3.64/1.00  
% 3.64/1.00  fof(f20,axiom,(
% 3.64/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f30,plain,(
% 3.64/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.64/1.00    inference(nnf_transformation,[],[f20])).
% 3.64/1.00  
% 3.64/1.00  fof(f31,plain,(
% 3.64/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.64/1.00    inference(flattening,[],[f30])).
% 3.64/1.00  
% 3.64/1.00  fof(f55,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.64/1.00    inference(cnf_transformation,[],[f31])).
% 3.64/1.00  
% 3.64/1.00  fof(f73,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X1))) )),
% 3.64/1.00    inference(definition_unfolding,[],[f55,f48,f48])).
% 3.64/1.00  
% 3.64/1.00  fof(f16,axiom,(
% 3.64/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f51,plain,(
% 3.64/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f16])).
% 3.64/1.00  
% 3.64/1.00  fof(f12,axiom,(
% 3.64/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f47,plain,(
% 3.64/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f12])).
% 3.64/1.00  
% 3.64/1.00  fof(f61,plain,(
% 3.64/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f47,f44,f48,f60])).
% 3.64/1.00  
% 3.64/1.00  fof(f17,axiom,(
% 3.64/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f52,plain,(
% 3.64/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f17])).
% 3.64/1.00  
% 3.64/1.00  fof(f18,axiom,(
% 3.64/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f53,plain,(
% 3.64/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f18])).
% 3.64/1.00  
% 3.64/1.00  fof(f19,axiom,(
% 3.64/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f54,plain,(
% 3.64/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f19])).
% 3.64/1.00  
% 3.64/1.00  fof(f62,plain,(
% 3.64/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f53,f54])).
% 3.64/1.00  
% 3.64/1.00  fof(f63,plain,(
% 3.64/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f52,f62])).
% 3.64/1.00  
% 3.64/1.00  fof(f70,plain,(
% 3.64/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f51,f61,f63])).
% 3.64/1.00  
% 3.64/1.00  fof(f56,plain,(
% 3.64/1.00    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 3.64/1.00    inference(cnf_transformation,[],[f31])).
% 3.64/1.00  
% 3.64/1.00  fof(f72,plain,(
% 3.64/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 != X0) )),
% 3.64/1.00    inference(definition_unfolding,[],[f56,f48])).
% 3.64/1.00  
% 3.64/1.00  fof(f79,plain,(
% 3.64/1.00    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X1))) )),
% 3.64/1.00    inference(equality_resolution,[],[f72])).
% 3.64/1.00  
% 3.64/1.00  fof(f2,axiom,(
% 3.64/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f28,plain,(
% 3.64/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.64/1.00    inference(nnf_transformation,[],[f2])).
% 3.64/1.00  
% 3.64/1.00  fof(f29,plain,(
% 3.64/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.64/1.00    inference(flattening,[],[f28])).
% 3.64/1.00  
% 3.64/1.00  fof(f37,plain,(
% 3.64/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f29])).
% 3.64/1.00  
% 3.64/1.00  fof(f7,axiom,(
% 3.64/1.00    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f25,plain,(
% 3.64/1.00    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.64/1.00    inference(ennf_transformation,[],[f7])).
% 3.64/1.00  
% 3.64/1.00  fof(f42,plain,(
% 3.64/1.00    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f25])).
% 3.64/1.00  
% 3.64/1.00  fof(f77,plain,(
% 3.64/1.00    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.64/1.00    inference(equality_resolution,[],[f42])).
% 3.64/1.00  
% 3.64/1.00  fof(f43,plain,(
% 3.64/1.00    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 3.64/1.00    inference(cnf_transformation,[],[f25])).
% 3.64/1.00  
% 3.64/1.00  fof(f35,plain,(
% 3.64/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.64/1.00    inference(cnf_transformation,[],[f29])).
% 3.64/1.00  
% 3.64/1.00  fof(f76,plain,(
% 3.64/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.64/1.00    inference(equality_resolution,[],[f35])).
% 3.64/1.00  
% 3.64/1.00  cnf(c_89,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_10,plain,
% 3.64/1.00      ( X0 = X1
% 3.64/1.00      | X2 = X1
% 3.64/1.00      | k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))),k2_tarski(X1,X1)) = k2_tarski(X0,X2) ),
% 3.64/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5493,plain,
% 3.64/1.00      ( ~ iProver_ARSWP_96
% 3.64/1.00      | X0 = X1
% 3.64/1.00      | X2 = X1
% 3.64/1.00      | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0 ),
% 3.64/1.00      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5629,plain,
% 3.64/1.00      ( X0 = X1
% 3.64/1.00      | X2 = X1
% 3.64/1.00      | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
% 3.64/1.00      | iProver_ARSWP_96 != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_5493]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_16,negated_conjecture,
% 3.64/1.00      ( sK0 != sK1 ),
% 3.64/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_140,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_614,plain,
% 3.64/1.00      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_140]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1738,plain,
% 3.64/1.00      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_140]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1946,plain,
% 3.64/1.00      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_1738]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1947,plain,
% 3.64/1.00      ( X0 != sK1 | sK1 = X0 ),
% 3.64/1.00      inference(equality_resolution_simp,[status(thm)],[c_1946]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5754,plain,
% 3.64/1.00      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_140]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5770,plain,
% 3.64/1.00      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_5754]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5771,plain,
% 3.64/1.00      ( X0 != sK0 | sK0 = X0 ),
% 3.64/1.00      inference(equality_resolution_simp,[status(thm)],[c_5770]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5777,plain,
% 3.64/1.00      ( k5_xboole_0(sK0,k1_xboole_0) != sK0
% 3.64/1.00      | sK0 = k5_xboole_0(sK0,k1_xboole_0) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_5771]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_7,plain,
% 3.64/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.64/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5783,plain,
% 3.64/1.00      ( k5_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5746,plain,
% 3.64/1.00      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_140]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5803,plain,
% 3.64/1.00      ( sK1 != k5_xboole_0(sK0,k1_xboole_0)
% 3.64/1.00      | sK0 != k5_xboole_0(sK0,k1_xboole_0)
% 3.64/1.00      | sK0 = sK1 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_5746]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5804,plain,
% 3.64/1.00      ( X0 != k5_xboole_0(sK0,k1_xboole_0)
% 3.64/1.00      | sK0 = X0
% 3.64/1.00      | sK0 != k5_xboole_0(sK0,k1_xboole_0) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_5754]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6017,plain,
% 3.64/1.00      ( ~ iProver_ARSWP_96
% 3.64/1.00      | X0 = sK1
% 3.64/1.00      | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
% 3.64/1.00      | sK0 = sK1 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_5493]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6018,plain,
% 3.64/1.00      ( X0 = sK1
% 3.64/1.00      | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
% 3.64/1.00      | sK0 = sK1
% 3.64/1.00      | iProver_ARSWP_96 != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_6017]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6042,plain,
% 3.64/1.00      ( ~ iProver_ARSWP_96
% 3.64/1.00      | X0 = k5_xboole_0(sK0,k1_xboole_0)
% 3.64/1.00      | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
% 3.64/1.00      | sK1 = k5_xboole_0(sK0,k1_xboole_0) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_5493]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6043,plain,
% 3.64/1.00      ( X0 = k5_xboole_0(sK0,k1_xboole_0)
% 3.64/1.00      | k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
% 3.64/1.00      | sK1 = k5_xboole_0(sK0,k1_xboole_0)
% 3.64/1.00      | iProver_ARSWP_96 != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_6042]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6588,plain,
% 3.64/1.00      ( k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0) = arAF0_k2_tarski_0
% 3.64/1.00      | iProver_ARSWP_96 != iProver_top ),
% 3.64/1.00      inference(global_propositional_subsumption,
% 3.64/1.00                [status(thm)],
% 3.64/1.00                [c_5629,c_16,c_614,c_1947,c_5777,c_5783,c_5803,c_5804,c_6018,
% 3.64/1.00                 c_6043]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2,plain,
% 3.64/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.64/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_0,plain,
% 3.64/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5910,plain,
% 3.64/1.00      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6,plain,
% 3.64/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.64/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5911,plain,
% 3.64/1.00      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5921,plain,
% 3.64/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_5911,c_7]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5913,plain,
% 3.64/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5915,plain,
% 3.64/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_5913,c_6]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5922,plain,
% 3.64/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_5921,c_5915]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5926,plain,
% 3.64/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_5910,c_5922]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6592,plain,
% 3.64/1.00      ( arAF0_k2_tarski_0 = k1_xboole_0 | iProver_ARSWP_96 != iProver_top ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_6588,c_7,c_5926]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_15,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
% 3.64/1.00      | k2_tarski(X1,X1) = X0
% 3.64/1.00      | k1_xboole_0 = X0 ),
% 3.64/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5498,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,arAF0_k2_tarski_0)
% 3.64/1.00      | ~ iProver_ARSWP_101
% 3.64/1.00      | arAF0_k2_tarski_0 = X0
% 3.64/1.00      | k1_xboole_0 = X0 ),
% 3.64/1.00      inference(arg_filter_abstr,[status(unp)],[c_15]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5624,plain,
% 3.64/1.00      ( arAF0_k2_tarski_0 = X0
% 3.64/1.00      | k1_xboole_0 = X0
% 3.64/1.00      | r1_tarski(X0,arAF0_k2_tarski_0) != iProver_top
% 3.64/1.00      | iProver_ARSWP_101 != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_5498]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6597,plain,
% 3.64/1.00      ( arAF0_k2_tarski_0 = X0
% 3.64/1.00      | k1_xboole_0 = X0
% 3.64/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.64/1.00      | iProver_ARSWP_101 != iProver_top
% 3.64/1.00      | iProver_ARSWP_96 != iProver_top ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_6592,c_5624]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_12,plain,
% 3.64/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
% 3.64/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5495,plain,
% 3.64/1.00      ( ~ iProver_ARSWP_98
% 3.64/1.00      | k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0)) = arAF0_k6_enumset1_0 ),
% 3.64/1.00      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5627,plain,
% 3.64/1.00      ( k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(k5_xboole_0(arAF0_k2_tarski_0,k4_xboole_0(arAF0_k2_tarski_0,arAF0_k2_tarski_0)),arAF0_k2_tarski_0)) = arAF0_k6_enumset1_0
% 3.64/1.00      | iProver_ARSWP_98 != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_5495]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6391,plain,
% 3.64/1.00      ( arAF0_k6_enumset1_0 = arAF0_k2_tarski_0
% 3.64/1.00      | iProver_ARSWP_98 != iProver_top ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_5627,c_7,c_5926]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_14,plain,
% 3.64/1.00      ( r1_tarski(k1_xboole_0,k2_tarski(X0,X0)) ),
% 3.64/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5497,plain,
% 3.64/1.00      ( r1_tarski(k1_xboole_0,arAF0_k2_tarski_0) | ~ iProver_ARSWP_100 ),
% 3.64/1.00      inference(arg_filter_abstr,[status(unp)],[c_14]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5625,plain,
% 3.64/1.00      ( r1_tarski(k1_xboole_0,arAF0_k2_tarski_0) = iProver_top
% 3.64/1.00      | iProver_ARSWP_100 != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_5497]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_3,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.64/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5635,plain,
% 3.64/1.00      ( X0 = X1
% 3.64/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.64/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6148,plain,
% 3.64/1.00      ( arAF0_k2_tarski_0 = k1_xboole_0
% 3.64/1.00      | r1_tarski(arAF0_k2_tarski_0,k1_xboole_0) != iProver_top
% 3.64/1.00      | iProver_ARSWP_100 != iProver_top ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_5625,c_5635]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_9,plain,
% 3.64/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5492,plain,
% 3.64/1.00      ( arAF0_r1_xboole_0_0_1(k1_xboole_0) | ~ iProver_ARSWP_95 ),
% 3.64/1.00      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5630,plain,
% 3.64/1.00      ( arAF0_r1_xboole_0_0_1(k1_xboole_0) = iProver_top
% 3.64/1.00      | iProver_ARSWP_95 != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_5492]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_8,plain,
% 3.64/1.00      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 3.64/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5491,plain,
% 3.64/1.00      ( ~ arAF0_r1_xboole_0_0_1(X0) | ~ iProver_ARSWP_94 | k1_xboole_0 = X0 ),
% 3.64/1.00      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5631,plain,
% 3.64/1.00      ( k1_xboole_0 = X0
% 3.64/1.00      | arAF0_r1_xboole_0_0_1(X0) != iProver_top
% 3.64/1.00      | iProver_ARSWP_94 != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_5491]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f76]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5634,plain,
% 3.64/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  % SZS output end Saturation for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  ------                               Statistics
% 3.64/1.00  
% 3.64/1.00  ------ Selected
% 3.64/1.00  
% 3.64/1.00  total_time:                             0.268
% 3.64/1.00  
%------------------------------------------------------------------------------
