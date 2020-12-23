%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:16 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 467 expanded)
%              Number of clauses        :   42 (  84 expanded)
%              Number of leaves         :   18 ( 149 expanded)
%              Depth                    :   16
%              Number of atoms          :  185 ( 648 expanded)
%              Number of equality atoms :  124 ( 570 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f66,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f61])).

fof(f67,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f66])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f46,f46])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f22,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 )
   => ( sK2 != sK3
      & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK2 != sK3
    & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f29])).

fof(f50,plain,(
    k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f50,f52,f52])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f38,f46,f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f68,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f51,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_452,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_450,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_825,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK3),k1_xboole_0) = k1_enumset1(sK3,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_15,c_1])).

cnf(c_921,plain,
    ( k1_enumset1(sK3,sK3,sK2) = k1_enumset1(sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_5,c_825])).

cnf(c_1073,plain,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_921,c_15])).

cnf(c_1112,plain,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_1073])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_456,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2120,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1112,c_456])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_620,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_630,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_620,c_5])).

cnf(c_2123,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
    | r1_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2120,c_630])).

cnf(c_2238,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_450,c_2123])).

cnf(c_2539,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_452,c_2238])).

cnf(c_1077,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK2),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(sK3,sK3,sK2))) = k1_enumset1(sK3,sK3,X0) ),
    inference(superposition,[status(thm)],[c_921,c_1])).

cnf(c_1091,plain,
    ( k1_enumset1(sK3,sK2,X0) = k1_enumset1(sK3,sK3,X0) ),
    inference(demodulation,[status(thm)],[c_1077,c_1])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_451,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1460,plain,
    ( sK3 = X0
    | r2_hidden(X0,k1_enumset1(sK3,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_451])).

cnf(c_1092,plain,
    ( k1_enumset1(sK3,sK2,sK3) = k1_enumset1(sK3,sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_1091,c_921])).

cnf(c_1107,plain,
    ( k1_enumset1(sK3,sK2,sK2) = k1_enumset1(sK3,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1092,c_1091])).

cnf(c_1115,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK2),k1_xboole_0) = k1_enumset1(sK3,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1073,c_1])).

cnf(c_1231,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0) = k1_enumset1(sK3,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_7,c_1115])).

cnf(c_1278,plain,
    ( k1_enumset1(sK2,sK2,sK3) = k1_enumset1(sK3,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_1231,c_5])).

cnf(c_1706,plain,
    ( k1_enumset1(sK2,sK2,sK3) = k1_enumset1(sK3,sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_1107,c_1278])).

cnf(c_2378,plain,
    ( sK3 = X0
    | r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1460,c_1706])).

cnf(c_3119,plain,
    ( sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_2539,c_2378])).

cnf(c_306,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_526,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_617,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_305,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_585,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_14,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3119,c_617,c_585,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:49:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.40/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/1.01  
% 2.40/1.01  ------  iProver source info
% 2.40/1.01  
% 2.40/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.40/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/1.01  git: non_committed_changes: false
% 2.40/1.01  git: last_make_outside_of_git: false
% 2.40/1.01  
% 2.40/1.01  ------ 
% 2.40/1.01  
% 2.40/1.01  ------ Input Options
% 2.40/1.01  
% 2.40/1.01  --out_options                           all
% 2.40/1.01  --tptp_safe_out                         true
% 2.40/1.01  --problem_path                          ""
% 2.40/1.01  --include_path                          ""
% 2.40/1.01  --clausifier                            res/vclausify_rel
% 2.40/1.01  --clausifier_options                    --mode clausify
% 2.40/1.01  --stdin                                 false
% 2.40/1.01  --stats_out                             all
% 2.40/1.01  
% 2.40/1.01  ------ General Options
% 2.40/1.01  
% 2.40/1.01  --fof                                   false
% 2.40/1.01  --time_out_real                         305.
% 2.40/1.01  --time_out_virtual                      -1.
% 2.40/1.01  --symbol_type_check                     false
% 2.40/1.01  --clausify_out                          false
% 2.40/1.01  --sig_cnt_out                           false
% 2.40/1.01  --trig_cnt_out                          false
% 2.40/1.01  --trig_cnt_out_tolerance                1.
% 2.40/1.01  --trig_cnt_out_sk_spl                   false
% 2.40/1.01  --abstr_cl_out                          false
% 2.40/1.01  
% 2.40/1.01  ------ Global Options
% 2.40/1.01  
% 2.40/1.01  --schedule                              default
% 2.40/1.01  --add_important_lit                     false
% 2.40/1.01  --prop_solver_per_cl                    1000
% 2.40/1.01  --min_unsat_core                        false
% 2.40/1.01  --soft_assumptions                      false
% 2.40/1.01  --soft_lemma_size                       3
% 2.40/1.01  --prop_impl_unit_size                   0
% 2.40/1.01  --prop_impl_unit                        []
% 2.40/1.01  --share_sel_clauses                     true
% 2.40/1.01  --reset_solvers                         false
% 2.40/1.01  --bc_imp_inh                            [conj_cone]
% 2.40/1.01  --conj_cone_tolerance                   3.
% 2.40/1.01  --extra_neg_conj                        none
% 2.40/1.01  --large_theory_mode                     true
% 2.40/1.01  --prolific_symb_bound                   200
% 2.40/1.01  --lt_threshold                          2000
% 2.40/1.01  --clause_weak_htbl                      true
% 2.40/1.01  --gc_record_bc_elim                     false
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing Options
% 2.40/1.01  
% 2.40/1.01  --preprocessing_flag                    true
% 2.40/1.01  --time_out_prep_mult                    0.1
% 2.40/1.01  --splitting_mode                        input
% 2.40/1.01  --splitting_grd                         true
% 2.40/1.01  --splitting_cvd                         false
% 2.40/1.01  --splitting_cvd_svl                     false
% 2.40/1.01  --splitting_nvd                         32
% 2.40/1.01  --sub_typing                            true
% 2.40/1.01  --prep_gs_sim                           true
% 2.40/1.01  --prep_unflatten                        true
% 2.40/1.01  --prep_res_sim                          true
% 2.40/1.01  --prep_upred                            true
% 2.40/1.01  --prep_sem_filter                       exhaustive
% 2.40/1.01  --prep_sem_filter_out                   false
% 2.40/1.01  --pred_elim                             true
% 2.40/1.01  --res_sim_input                         true
% 2.40/1.01  --eq_ax_congr_red                       true
% 2.40/1.01  --pure_diseq_elim                       true
% 2.40/1.01  --brand_transform                       false
% 2.40/1.01  --non_eq_to_eq                          false
% 2.40/1.01  --prep_def_merge                        true
% 2.40/1.01  --prep_def_merge_prop_impl              false
% 2.40/1.01  --prep_def_merge_mbd                    true
% 2.40/1.01  --prep_def_merge_tr_red                 false
% 2.40/1.01  --prep_def_merge_tr_cl                  false
% 2.40/1.01  --smt_preprocessing                     true
% 2.40/1.01  --smt_ac_axioms                         fast
% 2.40/1.01  --preprocessed_out                      false
% 2.40/1.01  --preprocessed_stats                    false
% 2.40/1.01  
% 2.40/1.01  ------ Abstraction refinement Options
% 2.40/1.01  
% 2.40/1.01  --abstr_ref                             []
% 2.40/1.01  --abstr_ref_prep                        false
% 2.40/1.01  --abstr_ref_until_sat                   false
% 2.40/1.01  --abstr_ref_sig_restrict                funpre
% 2.40/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/1.01  --abstr_ref_under                       []
% 2.40/1.01  
% 2.40/1.01  ------ SAT Options
% 2.40/1.01  
% 2.40/1.01  --sat_mode                              false
% 2.40/1.01  --sat_fm_restart_options                ""
% 2.40/1.01  --sat_gr_def                            false
% 2.40/1.01  --sat_epr_types                         true
% 2.40/1.01  --sat_non_cyclic_types                  false
% 2.40/1.01  --sat_finite_models                     false
% 2.40/1.01  --sat_fm_lemmas                         false
% 2.40/1.01  --sat_fm_prep                           false
% 2.40/1.01  --sat_fm_uc_incr                        true
% 2.40/1.01  --sat_out_model                         small
% 2.40/1.01  --sat_out_clauses                       false
% 2.40/1.01  
% 2.40/1.01  ------ QBF Options
% 2.40/1.01  
% 2.40/1.01  --qbf_mode                              false
% 2.40/1.01  --qbf_elim_univ                         false
% 2.40/1.01  --qbf_dom_inst                          none
% 2.40/1.01  --qbf_dom_pre_inst                      false
% 2.40/1.01  --qbf_sk_in                             false
% 2.40/1.01  --qbf_pred_elim                         true
% 2.40/1.01  --qbf_split                             512
% 2.40/1.01  
% 2.40/1.01  ------ BMC1 Options
% 2.40/1.01  
% 2.40/1.01  --bmc1_incremental                      false
% 2.40/1.01  --bmc1_axioms                           reachable_all
% 2.40/1.01  --bmc1_min_bound                        0
% 2.40/1.01  --bmc1_max_bound                        -1
% 2.40/1.01  --bmc1_max_bound_default                -1
% 2.40/1.01  --bmc1_symbol_reachability              true
% 2.40/1.01  --bmc1_property_lemmas                  false
% 2.40/1.01  --bmc1_k_induction                      false
% 2.40/1.01  --bmc1_non_equiv_states                 false
% 2.40/1.01  --bmc1_deadlock                         false
% 2.40/1.01  --bmc1_ucm                              false
% 2.40/1.01  --bmc1_add_unsat_core                   none
% 2.40/1.01  --bmc1_unsat_core_children              false
% 2.40/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/1.01  --bmc1_out_stat                         full
% 2.40/1.01  --bmc1_ground_init                      false
% 2.40/1.01  --bmc1_pre_inst_next_state              false
% 2.40/1.01  --bmc1_pre_inst_state                   false
% 2.40/1.01  --bmc1_pre_inst_reach_state             false
% 2.40/1.01  --bmc1_out_unsat_core                   false
% 2.40/1.01  --bmc1_aig_witness_out                  false
% 2.40/1.01  --bmc1_verbose                          false
% 2.40/1.01  --bmc1_dump_clauses_tptp                false
% 2.40/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.40/1.01  --bmc1_dump_file                        -
% 2.40/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.40/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.40/1.01  --bmc1_ucm_extend_mode                  1
% 2.40/1.01  --bmc1_ucm_init_mode                    2
% 2.40/1.01  --bmc1_ucm_cone_mode                    none
% 2.40/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.40/1.01  --bmc1_ucm_relax_model                  4
% 2.40/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.40/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/1.01  --bmc1_ucm_layered_model                none
% 2.40/1.01  --bmc1_ucm_max_lemma_size               10
% 2.40/1.01  
% 2.40/1.01  ------ AIG Options
% 2.40/1.01  
% 2.40/1.01  --aig_mode                              false
% 2.40/1.01  
% 2.40/1.01  ------ Instantiation Options
% 2.40/1.01  
% 2.40/1.01  --instantiation_flag                    true
% 2.40/1.01  --inst_sos_flag                         false
% 2.40/1.01  --inst_sos_phase                        true
% 2.40/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/1.01  --inst_lit_sel_side                     num_symb
% 2.40/1.01  --inst_solver_per_active                1400
% 2.40/1.01  --inst_solver_calls_frac                1.
% 2.40/1.01  --inst_passive_queue_type               priority_queues
% 2.40/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/1.01  --inst_passive_queues_freq              [25;2]
% 2.40/1.01  --inst_dismatching                      true
% 2.40/1.01  --inst_eager_unprocessed_to_passive     true
% 2.40/1.01  --inst_prop_sim_given                   true
% 2.40/1.01  --inst_prop_sim_new                     false
% 2.40/1.01  --inst_subs_new                         false
% 2.40/1.01  --inst_eq_res_simp                      false
% 2.40/1.01  --inst_subs_given                       false
% 2.40/1.01  --inst_orphan_elimination               true
% 2.40/1.01  --inst_learning_loop_flag               true
% 2.40/1.01  --inst_learning_start                   3000
% 2.40/1.01  --inst_learning_factor                  2
% 2.40/1.01  --inst_start_prop_sim_after_learn       3
% 2.40/1.01  --inst_sel_renew                        solver
% 2.40/1.01  --inst_lit_activity_flag                true
% 2.40/1.01  --inst_restr_to_given                   false
% 2.40/1.01  --inst_activity_threshold               500
% 2.40/1.01  --inst_out_proof                        true
% 2.40/1.01  
% 2.40/1.01  ------ Resolution Options
% 2.40/1.01  
% 2.40/1.01  --resolution_flag                       true
% 2.40/1.01  --res_lit_sel                           adaptive
% 2.40/1.01  --res_lit_sel_side                      none
% 2.40/1.01  --res_ordering                          kbo
% 2.40/1.01  --res_to_prop_solver                    active
% 2.40/1.01  --res_prop_simpl_new                    false
% 2.40/1.01  --res_prop_simpl_given                  true
% 2.40/1.01  --res_passive_queue_type                priority_queues
% 2.40/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/1.01  --res_passive_queues_freq               [15;5]
% 2.40/1.01  --res_forward_subs                      full
% 2.40/1.01  --res_backward_subs                     full
% 2.40/1.01  --res_forward_subs_resolution           true
% 2.40/1.01  --res_backward_subs_resolution          true
% 2.40/1.01  --res_orphan_elimination                true
% 2.40/1.01  --res_time_limit                        2.
% 2.40/1.01  --res_out_proof                         true
% 2.40/1.01  
% 2.40/1.01  ------ Superposition Options
% 2.40/1.01  
% 2.40/1.01  --superposition_flag                    true
% 2.40/1.01  --sup_passive_queue_type                priority_queues
% 2.40/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.40/1.01  --demod_completeness_check              fast
% 2.40/1.01  --demod_use_ground                      true
% 2.40/1.01  --sup_to_prop_solver                    passive
% 2.40/1.01  --sup_prop_simpl_new                    true
% 2.40/1.01  --sup_prop_simpl_given                  true
% 2.40/1.01  --sup_fun_splitting                     false
% 2.40/1.01  --sup_smt_interval                      50000
% 2.40/1.01  
% 2.40/1.01  ------ Superposition Simplification Setup
% 2.40/1.01  
% 2.40/1.01  --sup_indices_passive                   []
% 2.40/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_full_bw                           [BwDemod]
% 2.40/1.01  --sup_immed_triv                        [TrivRules]
% 2.40/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_immed_bw_main                     []
% 2.40/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  
% 2.40/1.01  ------ Combination Options
% 2.40/1.01  
% 2.40/1.01  --comb_res_mult                         3
% 2.40/1.01  --comb_sup_mult                         2
% 2.40/1.01  --comb_inst_mult                        10
% 2.40/1.01  
% 2.40/1.01  ------ Debug Options
% 2.40/1.01  
% 2.40/1.01  --dbg_backtrace                         false
% 2.40/1.01  --dbg_dump_prop_clauses                 false
% 2.40/1.01  --dbg_dump_prop_clauses_file            -
% 2.40/1.01  --dbg_out_stat                          false
% 2.40/1.01  ------ Parsing...
% 2.40/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/1.01  ------ Proving...
% 2.40/1.01  ------ Problem Properties 
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  clauses                                 16
% 2.40/1.01  conjectures                             2
% 2.40/1.01  EPR                                     1
% 2.40/1.01  Horn                                    13
% 2.40/1.01  unary                                   10
% 2.40/1.01  binary                                  4
% 2.40/1.01  lits                                    24
% 2.40/1.01  lits eq                                 14
% 2.40/1.01  fd_pure                                 0
% 2.40/1.01  fd_pseudo                               0
% 2.40/1.01  fd_cond                                 0
% 2.40/1.01  fd_pseudo_cond                          2
% 2.40/1.01  AC symbols                              0
% 2.40/1.01  
% 2.40/1.01  ------ Schedule dynamic 5 is on 
% 2.40/1.01  
% 2.40/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  ------ 
% 2.40/1.01  Current options:
% 2.40/1.01  ------ 
% 2.40/1.01  
% 2.40/1.01  ------ Input Options
% 2.40/1.01  
% 2.40/1.01  --out_options                           all
% 2.40/1.01  --tptp_safe_out                         true
% 2.40/1.01  --problem_path                          ""
% 2.40/1.01  --include_path                          ""
% 2.40/1.01  --clausifier                            res/vclausify_rel
% 2.40/1.01  --clausifier_options                    --mode clausify
% 2.40/1.01  --stdin                                 false
% 2.40/1.01  --stats_out                             all
% 2.40/1.01  
% 2.40/1.01  ------ General Options
% 2.40/1.01  
% 2.40/1.01  --fof                                   false
% 2.40/1.01  --time_out_real                         305.
% 2.40/1.01  --time_out_virtual                      -1.
% 2.40/1.01  --symbol_type_check                     false
% 2.40/1.01  --clausify_out                          false
% 2.40/1.01  --sig_cnt_out                           false
% 2.40/1.01  --trig_cnt_out                          false
% 2.40/1.01  --trig_cnt_out_tolerance                1.
% 2.40/1.01  --trig_cnt_out_sk_spl                   false
% 2.40/1.01  --abstr_cl_out                          false
% 2.40/1.01  
% 2.40/1.01  ------ Global Options
% 2.40/1.01  
% 2.40/1.01  --schedule                              default
% 2.40/1.01  --add_important_lit                     false
% 2.40/1.01  --prop_solver_per_cl                    1000
% 2.40/1.01  --min_unsat_core                        false
% 2.40/1.01  --soft_assumptions                      false
% 2.40/1.01  --soft_lemma_size                       3
% 2.40/1.01  --prop_impl_unit_size                   0
% 2.40/1.01  --prop_impl_unit                        []
% 2.40/1.01  --share_sel_clauses                     true
% 2.40/1.01  --reset_solvers                         false
% 2.40/1.01  --bc_imp_inh                            [conj_cone]
% 2.40/1.01  --conj_cone_tolerance                   3.
% 2.40/1.01  --extra_neg_conj                        none
% 2.40/1.01  --large_theory_mode                     true
% 2.40/1.01  --prolific_symb_bound                   200
% 2.40/1.01  --lt_threshold                          2000
% 2.40/1.01  --clause_weak_htbl                      true
% 2.40/1.01  --gc_record_bc_elim                     false
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing Options
% 2.40/1.01  
% 2.40/1.01  --preprocessing_flag                    true
% 2.40/1.01  --time_out_prep_mult                    0.1
% 2.40/1.01  --splitting_mode                        input
% 2.40/1.01  --splitting_grd                         true
% 2.40/1.01  --splitting_cvd                         false
% 2.40/1.01  --splitting_cvd_svl                     false
% 2.40/1.01  --splitting_nvd                         32
% 2.40/1.01  --sub_typing                            true
% 2.40/1.01  --prep_gs_sim                           true
% 2.40/1.01  --prep_unflatten                        true
% 2.40/1.01  --prep_res_sim                          true
% 2.40/1.01  --prep_upred                            true
% 2.40/1.01  --prep_sem_filter                       exhaustive
% 2.40/1.01  --prep_sem_filter_out                   false
% 2.40/1.01  --pred_elim                             true
% 2.40/1.01  --res_sim_input                         true
% 2.40/1.01  --eq_ax_congr_red                       true
% 2.40/1.01  --pure_diseq_elim                       true
% 2.40/1.01  --brand_transform                       false
% 2.40/1.01  --non_eq_to_eq                          false
% 2.40/1.01  --prep_def_merge                        true
% 2.40/1.01  --prep_def_merge_prop_impl              false
% 2.40/1.01  --prep_def_merge_mbd                    true
% 2.40/1.01  --prep_def_merge_tr_red                 false
% 2.40/1.01  --prep_def_merge_tr_cl                  false
% 2.40/1.01  --smt_preprocessing                     true
% 2.40/1.01  --smt_ac_axioms                         fast
% 2.40/1.01  --preprocessed_out                      false
% 2.40/1.01  --preprocessed_stats                    false
% 2.40/1.01  
% 2.40/1.01  ------ Abstraction refinement Options
% 2.40/1.01  
% 2.40/1.01  --abstr_ref                             []
% 2.40/1.01  --abstr_ref_prep                        false
% 2.40/1.01  --abstr_ref_until_sat                   false
% 2.40/1.01  --abstr_ref_sig_restrict                funpre
% 2.40/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/1.01  --abstr_ref_under                       []
% 2.40/1.01  
% 2.40/1.01  ------ SAT Options
% 2.40/1.01  
% 2.40/1.01  --sat_mode                              false
% 2.40/1.01  --sat_fm_restart_options                ""
% 2.40/1.01  --sat_gr_def                            false
% 2.40/1.01  --sat_epr_types                         true
% 2.40/1.01  --sat_non_cyclic_types                  false
% 2.40/1.01  --sat_finite_models                     false
% 2.40/1.01  --sat_fm_lemmas                         false
% 2.40/1.01  --sat_fm_prep                           false
% 2.40/1.01  --sat_fm_uc_incr                        true
% 2.40/1.01  --sat_out_model                         small
% 2.40/1.01  --sat_out_clauses                       false
% 2.40/1.01  
% 2.40/1.01  ------ QBF Options
% 2.40/1.01  
% 2.40/1.01  --qbf_mode                              false
% 2.40/1.01  --qbf_elim_univ                         false
% 2.40/1.01  --qbf_dom_inst                          none
% 2.40/1.01  --qbf_dom_pre_inst                      false
% 2.40/1.01  --qbf_sk_in                             false
% 2.40/1.01  --qbf_pred_elim                         true
% 2.40/1.01  --qbf_split                             512
% 2.40/1.01  
% 2.40/1.01  ------ BMC1 Options
% 2.40/1.01  
% 2.40/1.01  --bmc1_incremental                      false
% 2.40/1.01  --bmc1_axioms                           reachable_all
% 2.40/1.01  --bmc1_min_bound                        0
% 2.40/1.01  --bmc1_max_bound                        -1
% 2.40/1.01  --bmc1_max_bound_default                -1
% 2.40/1.01  --bmc1_symbol_reachability              true
% 2.40/1.01  --bmc1_property_lemmas                  false
% 2.40/1.01  --bmc1_k_induction                      false
% 2.40/1.01  --bmc1_non_equiv_states                 false
% 2.40/1.01  --bmc1_deadlock                         false
% 2.40/1.01  --bmc1_ucm                              false
% 2.40/1.01  --bmc1_add_unsat_core                   none
% 2.40/1.01  --bmc1_unsat_core_children              false
% 2.40/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/1.01  --bmc1_out_stat                         full
% 2.40/1.01  --bmc1_ground_init                      false
% 2.40/1.01  --bmc1_pre_inst_next_state              false
% 2.40/1.01  --bmc1_pre_inst_state                   false
% 2.40/1.01  --bmc1_pre_inst_reach_state             false
% 2.40/1.01  --bmc1_out_unsat_core                   false
% 2.40/1.01  --bmc1_aig_witness_out                  false
% 2.40/1.01  --bmc1_verbose                          false
% 2.40/1.01  --bmc1_dump_clauses_tptp                false
% 2.40/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.40/1.01  --bmc1_dump_file                        -
% 2.40/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.40/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.40/1.01  --bmc1_ucm_extend_mode                  1
% 2.40/1.01  --bmc1_ucm_init_mode                    2
% 2.40/1.01  --bmc1_ucm_cone_mode                    none
% 2.40/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.40/1.01  --bmc1_ucm_relax_model                  4
% 2.40/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.40/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/1.01  --bmc1_ucm_layered_model                none
% 2.40/1.01  --bmc1_ucm_max_lemma_size               10
% 2.40/1.01  
% 2.40/1.01  ------ AIG Options
% 2.40/1.01  
% 2.40/1.01  --aig_mode                              false
% 2.40/1.01  
% 2.40/1.01  ------ Instantiation Options
% 2.40/1.01  
% 2.40/1.01  --instantiation_flag                    true
% 2.40/1.01  --inst_sos_flag                         false
% 2.40/1.01  --inst_sos_phase                        true
% 2.40/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/1.01  --inst_lit_sel_side                     none
% 2.40/1.01  --inst_solver_per_active                1400
% 2.40/1.01  --inst_solver_calls_frac                1.
% 2.40/1.01  --inst_passive_queue_type               priority_queues
% 2.40/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/1.01  --inst_passive_queues_freq              [25;2]
% 2.40/1.01  --inst_dismatching                      true
% 2.40/1.01  --inst_eager_unprocessed_to_passive     true
% 2.40/1.01  --inst_prop_sim_given                   true
% 2.40/1.01  --inst_prop_sim_new                     false
% 2.40/1.01  --inst_subs_new                         false
% 2.40/1.01  --inst_eq_res_simp                      false
% 2.40/1.01  --inst_subs_given                       false
% 2.40/1.01  --inst_orphan_elimination               true
% 2.40/1.01  --inst_learning_loop_flag               true
% 2.40/1.01  --inst_learning_start                   3000
% 2.40/1.01  --inst_learning_factor                  2
% 2.40/1.01  --inst_start_prop_sim_after_learn       3
% 2.40/1.01  --inst_sel_renew                        solver
% 2.40/1.01  --inst_lit_activity_flag                true
% 2.40/1.01  --inst_restr_to_given                   false
% 2.40/1.01  --inst_activity_threshold               500
% 2.40/1.01  --inst_out_proof                        true
% 2.40/1.01  
% 2.40/1.01  ------ Resolution Options
% 2.40/1.01  
% 2.40/1.01  --resolution_flag                       false
% 2.40/1.01  --res_lit_sel                           adaptive
% 2.40/1.01  --res_lit_sel_side                      none
% 2.40/1.01  --res_ordering                          kbo
% 2.40/1.01  --res_to_prop_solver                    active
% 2.40/1.01  --res_prop_simpl_new                    false
% 2.40/1.01  --res_prop_simpl_given                  true
% 2.40/1.01  --res_passive_queue_type                priority_queues
% 2.40/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/1.01  --res_passive_queues_freq               [15;5]
% 2.40/1.01  --res_forward_subs                      full
% 2.40/1.01  --res_backward_subs                     full
% 2.40/1.01  --res_forward_subs_resolution           true
% 2.40/1.01  --res_backward_subs_resolution          true
% 2.40/1.01  --res_orphan_elimination                true
% 2.40/1.01  --res_time_limit                        2.
% 2.40/1.01  --res_out_proof                         true
% 2.40/1.01  
% 2.40/1.01  ------ Superposition Options
% 2.40/1.01  
% 2.40/1.01  --superposition_flag                    true
% 2.40/1.01  --sup_passive_queue_type                priority_queues
% 2.40/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.40/1.01  --demod_completeness_check              fast
% 2.40/1.01  --demod_use_ground                      true
% 2.40/1.01  --sup_to_prop_solver                    passive
% 2.40/1.01  --sup_prop_simpl_new                    true
% 2.40/1.01  --sup_prop_simpl_given                  true
% 2.40/1.01  --sup_fun_splitting                     false
% 2.40/1.01  --sup_smt_interval                      50000
% 2.40/1.01  
% 2.40/1.01  ------ Superposition Simplification Setup
% 2.40/1.01  
% 2.40/1.01  --sup_indices_passive                   []
% 2.40/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_full_bw                           [BwDemod]
% 2.40/1.01  --sup_immed_triv                        [TrivRules]
% 2.40/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_immed_bw_main                     []
% 2.40/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  
% 2.40/1.01  ------ Combination Options
% 2.40/1.01  
% 2.40/1.01  --comb_res_mult                         3
% 2.40/1.01  --comb_sup_mult                         2
% 2.40/1.01  --comb_inst_mult                        10
% 2.40/1.01  
% 2.40/1.01  ------ Debug Options
% 2.40/1.01  
% 2.40/1.01  --dbg_backtrace                         false
% 2.40/1.01  --dbg_dump_prop_clauses                 false
% 2.40/1.01  --dbg_dump_prop_clauses_file            -
% 2.40/1.01  --dbg_out_stat                          false
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  ------ Proving...
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  % SZS status Theorem for theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  fof(f10,axiom,(
% 2.40/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f25,plain,(
% 2.40/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.40/1.01    inference(nnf_transformation,[],[f10])).
% 2.40/1.01  
% 2.40/1.01  fof(f26,plain,(
% 2.40/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.40/1.01    inference(rectify,[],[f25])).
% 2.40/1.01  
% 2.40/1.01  fof(f27,plain,(
% 2.40/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f28,plain,(
% 2.40/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.40/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.40/1.01  
% 2.40/1.01  fof(f41,plain,(
% 2.40/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.40/1.01    inference(cnf_transformation,[],[f28])).
% 2.40/1.01  
% 2.40/1.01  fof(f12,axiom,(
% 2.40/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f45,plain,(
% 2.40/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f12])).
% 2.40/1.01  
% 2.40/1.01  fof(f13,axiom,(
% 2.40/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f46,plain,(
% 2.40/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f13])).
% 2.40/1.01  
% 2.40/1.01  fof(f52,plain,(
% 2.40/1.01    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.40/1.01    inference(definition_unfolding,[],[f45,f46])).
% 2.40/1.01  
% 2.40/1.01  fof(f61,plain,(
% 2.40/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 2.40/1.01    inference(definition_unfolding,[],[f41,f52])).
% 2.40/1.01  
% 2.40/1.01  fof(f66,plain,(
% 2.40/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 2.40/1.01    inference(equality_resolution,[],[f61])).
% 2.40/1.01  
% 2.40/1.01  fof(f67,plain,(
% 2.40/1.01    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 2.40/1.01    inference(equality_resolution,[],[f66])).
% 2.40/1.01  
% 2.40/1.01  fof(f16,axiom,(
% 2.40/1.01    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f21,plain,(
% 2.40/1.01    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.40/1.01    inference(ennf_transformation,[],[f16])).
% 2.40/1.01  
% 2.40/1.01  fof(f49,plain,(
% 2.40/1.01    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f21])).
% 2.40/1.01  
% 2.40/1.01  fof(f64,plain,(
% 2.40/1.01    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.40/1.01    inference(definition_unfolding,[],[f49,f52])).
% 2.40/1.01  
% 2.40/1.01  fof(f9,axiom,(
% 2.40/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f39,plain,(
% 2.40/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f9])).
% 2.40/1.01  
% 2.40/1.01  fof(f58,plain,(
% 2.40/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.40/1.01    inference(definition_unfolding,[],[f39,f46,f46])).
% 2.40/1.01  
% 2.40/1.01  fof(f6,axiom,(
% 2.40/1.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f36,plain,(
% 2.40/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.40/1.01    inference(cnf_transformation,[],[f6])).
% 2.40/1.01  
% 2.40/1.01  fof(f17,conjecture,(
% 2.40/1.01    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 => X0 = X1)),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f18,negated_conjecture,(
% 2.40/1.01    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 => X0 = X1)),
% 2.40/1.01    inference(negated_conjecture,[],[f17])).
% 2.40/1.01  
% 2.40/1.01  fof(f22,plain,(
% 2.40/1.01    ? [X0,X1] : (X0 != X1 & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0)),
% 2.40/1.01    inference(ennf_transformation,[],[f18])).
% 2.40/1.01  
% 2.40/1.01  fof(f29,plain,(
% 2.40/1.01    ? [X0,X1] : (X0 != X1 & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0) => (sK2 != sK3 & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0)),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f30,plain,(
% 2.40/1.01    sK2 != sK3 & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0),
% 2.40/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f29])).
% 2.40/1.01  
% 2.40/1.01  fof(f50,plain,(
% 2.40/1.01    k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0),
% 2.40/1.01    inference(cnf_transformation,[],[f30])).
% 2.40/1.01  
% 2.40/1.01  fof(f65,plain,(
% 2.40/1.01    k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_xboole_0),
% 2.40/1.01    inference(definition_unfolding,[],[f50,f52,f52])).
% 2.40/1.01  
% 2.40/1.01  fof(f11,axiom,(
% 2.40/1.01    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f44,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f11])).
% 2.40/1.01  
% 2.40/1.01  fof(f8,axiom,(
% 2.40/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f38,plain,(
% 2.40/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f8])).
% 2.40/1.01  
% 2.40/1.01  fof(f54,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2)) )),
% 2.40/1.01    inference(definition_unfolding,[],[f44,f38,f46,f52])).
% 2.40/1.01  
% 2.40/1.01  fof(f2,axiom,(
% 2.40/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f19,plain,(
% 2.40/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.40/1.01    inference(rectify,[],[f2])).
% 2.40/1.01  
% 2.40/1.01  fof(f20,plain,(
% 2.40/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.40/1.01    inference(ennf_transformation,[],[f19])).
% 2.40/1.01  
% 2.40/1.01  fof(f23,plain,(
% 2.40/1.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f24,plain,(
% 2.40/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.40/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).
% 2.40/1.01  
% 2.40/1.01  fof(f32,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.40/1.01    inference(cnf_transformation,[],[f24])).
% 2.40/1.01  
% 2.40/1.01  fof(f5,axiom,(
% 2.40/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f35,plain,(
% 2.40/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.40/1.01    inference(cnf_transformation,[],[f5])).
% 2.40/1.01  
% 2.40/1.01  fof(f55,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.40/1.01    inference(definition_unfolding,[],[f32,f35])).
% 2.40/1.01  
% 2.40/1.01  fof(f4,axiom,(
% 2.40/1.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f34,plain,(
% 2.40/1.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.40/1.01    inference(cnf_transformation,[],[f4])).
% 2.40/1.01  
% 2.40/1.01  fof(f57,plain,(
% 2.40/1.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 2.40/1.01    inference(definition_unfolding,[],[f34,f35])).
% 2.40/1.01  
% 2.40/1.01  fof(f3,axiom,(
% 2.40/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f33,plain,(
% 2.40/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.40/1.01    inference(cnf_transformation,[],[f3])).
% 2.40/1.01  
% 2.40/1.01  fof(f53,plain,(
% 2.40/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.40/1.01    inference(definition_unfolding,[],[f33,f35])).
% 2.40/1.01  
% 2.40/1.01  fof(f40,plain,(
% 2.40/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.40/1.01    inference(cnf_transformation,[],[f28])).
% 2.40/1.01  
% 2.40/1.01  fof(f62,plain,(
% 2.40/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 2.40/1.01    inference(definition_unfolding,[],[f40,f52])).
% 2.40/1.01  
% 2.40/1.01  fof(f68,plain,(
% 2.40/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 2.40/1.01    inference(equality_resolution,[],[f62])).
% 2.40/1.01  
% 2.40/1.01  fof(f51,plain,(
% 2.40/1.01    sK2 != sK3),
% 2.40/1.01    inference(cnf_transformation,[],[f30])).
% 2.40/1.01  
% 2.40/1.01  cnf(c_10,plain,
% 2.40/1.01      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 2.40/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_452,plain,
% 2.40/1.01      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_13,plain,
% 2.40/1.01      ( r2_hidden(X0,X1) | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
% 2.40/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_450,plain,
% 2.40/1.01      ( r2_hidden(X0,X1) = iProver_top
% 2.40/1.01      | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_7,plain,
% 2.40/1.01      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_5,plain,
% 2.40/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.40/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_15,negated_conjecture,
% 2.40/1.01      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)) = k1_xboole_0 ),
% 2.40/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1,plain,
% 2.40/1.01      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) = k1_enumset1(X0,X1,X2) ),
% 2.40/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_825,plain,
% 2.40/1.01      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK3),k1_xboole_0) = k1_enumset1(sK3,sK3,sK2) ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_15,c_1]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_921,plain,
% 2.40/1.01      ( k1_enumset1(sK3,sK3,sK2) = k1_enumset1(sK3,sK3,sK3) ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_5,c_825]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1073,plain,
% 2.40/1.01      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK2)) = k1_xboole_0 ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_921,c_15]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1112,plain,
% 2.40/1.01      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) = k1_xboole_0 ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_7,c_1073]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2,plain,
% 2.40/1.01      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 2.40/1.01      | ~ r1_xboole_0(X1,X2) ),
% 2.40/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_456,plain,
% 2.40/1.01      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 2.40/1.01      | r1_xboole_0(X1,X2) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2120,plain,
% 2.40/1.01      ( r2_hidden(X0,k4_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_xboole_0)) != iProver_top
% 2.40/1.01      | r1_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_1112,c_456]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_4,plain,
% 2.40/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.40/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_0,plain,
% 2.40/1.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.40/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_620,plain,
% 2.40/1.01      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_630,plain,
% 2.40/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.40/1.01      inference(light_normalisation,[status(thm)],[c_620,c_5]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2123,plain,
% 2.40/1.01      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
% 2.40/1.01      | r1_xboole_0(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_2120,c_630]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2238,plain,
% 2.40/1.01      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
% 2.40/1.01      | r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_450,c_2123]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2539,plain,
% 2.40/1.01      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_452,c_2238]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1077,plain,
% 2.40/1.01      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK2),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(sK3,sK3,sK2))) = k1_enumset1(sK3,sK3,X0) ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_921,c_1]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1091,plain,
% 2.40/1.01      ( k1_enumset1(sK3,sK2,X0) = k1_enumset1(sK3,sK3,X0) ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_1077,c_1]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_11,plain,
% 2.40/1.01      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 2.40/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_451,plain,
% 2.40/1.01      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1460,plain,
% 2.40/1.01      ( sK3 = X0
% 2.40/1.01      | r2_hidden(X0,k1_enumset1(sK3,sK2,sK3)) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_1091,c_451]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1092,plain,
% 2.40/1.01      ( k1_enumset1(sK3,sK2,sK3) = k1_enumset1(sK3,sK3,sK2) ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_1091,c_921]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1107,plain,
% 2.40/1.01      ( k1_enumset1(sK3,sK2,sK2) = k1_enumset1(sK3,sK2,sK3) ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_1092,c_1091]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1115,plain,
% 2.40/1.01      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK2),k1_xboole_0) = k1_enumset1(sK3,sK2,sK2) ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_1073,c_1]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1231,plain,
% 2.40/1.01      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0) = k1_enumset1(sK3,sK2,sK2) ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_7,c_1115]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1278,plain,
% 2.40/1.01      ( k1_enumset1(sK2,sK2,sK3) = k1_enumset1(sK3,sK2,sK2) ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_1231,c_5]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1706,plain,
% 2.40/1.01      ( k1_enumset1(sK2,sK2,sK3) = k1_enumset1(sK3,sK2,sK3) ),
% 2.40/1.01      inference(light_normalisation,[status(thm)],[c_1107,c_1278]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2378,plain,
% 2.40/1.01      ( sK3 = X0
% 2.40/1.01      | r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top ),
% 2.40/1.01      inference(light_normalisation,[status(thm)],[c_1460,c_1706]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3119,plain,
% 2.40/1.01      ( sK3 = sK2 ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_2539,c_2378]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_306,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_526,plain,
% 2.40/1.01      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 2.40/1.01      inference(instantiation,[status(thm)],[c_306]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_617,plain,
% 2.40/1.01      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 2.40/1.01      inference(instantiation,[status(thm)],[c_526]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_305,plain,( X0 = X0 ),theory(equality) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_585,plain,
% 2.40/1.01      ( sK2 = sK2 ),
% 2.40/1.01      inference(instantiation,[status(thm)],[c_305]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_14,negated_conjecture,
% 2.40/1.01      ( sK2 != sK3 ),
% 2.40/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(contradiction,plain,
% 2.40/1.01      ( $false ),
% 2.40/1.01      inference(minisat,[status(thm)],[c_3119,c_617,c_585,c_14]) ).
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  ------                               Statistics
% 2.40/1.01  
% 2.40/1.01  ------ General
% 2.40/1.01  
% 2.40/1.01  abstr_ref_over_cycles:                  0
% 2.40/1.01  abstr_ref_under_cycles:                 0
% 2.40/1.01  gc_basic_clause_elim:                   0
% 2.40/1.01  forced_gc_time:                         0
% 2.40/1.01  parsing_time:                           0.008
% 2.40/1.01  unif_index_cands_time:                  0.
% 2.40/1.01  unif_index_add_time:                    0.
% 2.40/1.01  orderings_time:                         0.
% 2.40/1.01  out_proof_time:                         0.009
% 2.40/1.01  total_time:                             0.13
% 2.40/1.01  num_of_symbols:                         42
% 2.40/1.01  num_of_terms:                           3175
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing
% 2.40/1.01  
% 2.40/1.01  num_of_splits:                          0
% 2.40/1.01  num_of_split_atoms:                     0
% 2.40/1.01  num_of_reused_defs:                     0
% 2.40/1.01  num_eq_ax_congr_red:                    20
% 2.40/1.01  num_of_sem_filtered_clauses:            1
% 2.40/1.01  num_of_subtypes:                        0
% 2.40/1.01  monotx_restored_types:                  0
% 2.40/1.01  sat_num_of_epr_types:                   0
% 2.40/1.01  sat_num_of_non_cyclic_types:            0
% 2.40/1.01  sat_guarded_non_collapsed_types:        0
% 2.40/1.01  num_pure_diseq_elim:                    0
% 2.40/1.01  simp_replaced_by:                       0
% 2.40/1.01  res_preprocessed:                       63
% 2.40/1.01  prep_upred:                             0
% 2.40/1.01  prep_unflattend:                        20
% 2.40/1.01  smt_new_axioms:                         0
% 2.40/1.01  pred_elim_cands:                        2
% 2.40/1.01  pred_elim:                              0
% 2.40/1.01  pred_elim_cl:                           0
% 2.40/1.01  pred_elim_cycles:                       2
% 2.40/1.01  merged_defs:                            0
% 2.40/1.01  merged_defs_ncl:                        0
% 2.40/1.01  bin_hyper_res:                          0
% 2.40/1.01  prep_cycles:                            3
% 2.40/1.01  pred_elim_time:                         0.003
% 2.40/1.01  splitting_time:                         0.
% 2.40/1.01  sem_filter_time:                        0.
% 2.40/1.01  monotx_time:                            0.
% 2.40/1.01  subtype_inf_time:                       0.
% 2.40/1.01  
% 2.40/1.01  ------ Problem properties
% 2.40/1.01  
% 2.40/1.01  clauses:                                16
% 2.40/1.01  conjectures:                            2
% 2.40/1.01  epr:                                    1
% 2.40/1.01  horn:                                   13
% 2.40/1.01  ground:                                 2
% 2.40/1.01  unary:                                  10
% 2.40/1.01  binary:                                 4
% 2.40/1.01  lits:                                   24
% 2.40/1.01  lits_eq:                                14
% 2.40/1.01  fd_pure:                                0
% 2.40/1.01  fd_pseudo:                              0
% 2.40/1.01  fd_cond:                                0
% 2.40/1.01  fd_pseudo_cond:                         2
% 2.40/1.01  ac_symbols:                             0
% 2.40/1.01  
% 2.40/1.01  ------ Propositional Solver
% 2.40/1.01  
% 2.40/1.01  prop_solver_calls:                      26
% 2.40/1.01  prop_fast_solver_calls:                 345
% 2.40/1.01  smt_solver_calls:                       0
% 2.40/1.01  smt_fast_solver_calls:                  0
% 2.40/1.01  prop_num_of_clauses:                    1287
% 2.40/1.01  prop_preprocess_simplified:             2961
% 2.40/1.01  prop_fo_subsumed:                       1
% 2.40/1.01  prop_solver_time:                       0.
% 2.40/1.01  smt_solver_time:                        0.
% 2.40/1.01  smt_fast_solver_time:                   0.
% 2.40/1.01  prop_fast_solver_time:                  0.
% 2.40/1.01  prop_unsat_core_time:                   0.
% 2.40/1.01  
% 2.40/1.01  ------ QBF
% 2.40/1.01  
% 2.40/1.01  qbf_q_res:                              0
% 2.40/1.01  qbf_num_tautologies:                    0
% 2.40/1.01  qbf_prep_cycles:                        0
% 2.40/1.01  
% 2.40/1.01  ------ BMC1
% 2.40/1.01  
% 2.40/1.01  bmc1_current_bound:                     -1
% 2.40/1.01  bmc1_last_solved_bound:                 -1
% 2.40/1.01  bmc1_unsat_core_size:                   -1
% 2.40/1.01  bmc1_unsat_core_parents_size:           -1
% 2.40/1.01  bmc1_merge_next_fun:                    0
% 2.40/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.40/1.01  
% 2.40/1.01  ------ Instantiation
% 2.40/1.01  
% 2.40/1.01  inst_num_of_clauses:                    395
% 2.40/1.01  inst_num_in_passive:                    90
% 2.40/1.01  inst_num_in_active:                     172
% 2.40/1.01  inst_num_in_unprocessed:                133
% 2.40/1.01  inst_num_of_loops:                      240
% 2.40/1.01  inst_num_of_learning_restarts:          0
% 2.40/1.01  inst_num_moves_active_passive:          63
% 2.40/1.01  inst_lit_activity:                      0
% 2.40/1.01  inst_lit_activity_moves:                0
% 2.40/1.01  inst_num_tautologies:                   0
% 2.40/1.01  inst_num_prop_implied:                  0
% 2.40/1.01  inst_num_existing_simplified:           0
% 2.40/1.01  inst_num_eq_res_simplified:             0
% 2.40/1.01  inst_num_child_elim:                    0
% 2.40/1.01  inst_num_of_dismatching_blockings:      141
% 2.40/1.01  inst_num_of_non_proper_insts:           429
% 2.40/1.01  inst_num_of_duplicates:                 0
% 2.40/1.01  inst_inst_num_from_inst_to_res:         0
% 2.40/1.01  inst_dismatching_checking_time:         0.
% 2.40/1.01  
% 2.40/1.01  ------ Resolution
% 2.40/1.01  
% 2.40/1.01  res_num_of_clauses:                     0
% 2.40/1.01  res_num_in_passive:                     0
% 2.40/1.01  res_num_in_active:                      0
% 2.40/1.01  res_num_of_loops:                       66
% 2.40/1.01  res_forward_subset_subsumed:            34
% 2.40/1.01  res_backward_subset_subsumed:           0
% 2.40/1.01  res_forward_subsumed:                   0
% 2.40/1.01  res_backward_subsumed:                  0
% 2.40/1.01  res_forward_subsumption_resolution:     0
% 2.40/1.01  res_backward_subsumption_resolution:    0
% 2.40/1.01  res_clause_to_clause_subsumption:       254
% 2.40/1.01  res_orphan_elimination:                 0
% 2.40/1.01  res_tautology_del:                      59
% 2.40/1.01  res_num_eq_res_simplified:              0
% 2.40/1.01  res_num_sel_changes:                    0
% 2.40/1.01  res_moves_from_active_to_pass:          0
% 2.40/1.01  
% 2.40/1.01  ------ Superposition
% 2.40/1.01  
% 2.40/1.01  sup_time_total:                         0.
% 2.40/1.01  sup_time_generating:                    0.
% 2.40/1.01  sup_time_sim_full:                      0.
% 2.40/1.01  sup_time_sim_immed:                     0.
% 2.40/1.01  
% 2.40/1.01  sup_num_of_clauses:                     61
% 2.40/1.01  sup_num_in_active:                      35
% 2.40/1.01  sup_num_in_passive:                     26
% 2.40/1.01  sup_num_of_loops:                       47
% 2.40/1.01  sup_fw_superposition:                   88
% 2.40/1.01  sup_bw_superposition:                   63
% 2.40/1.01  sup_immediate_simplified:               42
% 2.40/1.01  sup_given_eliminated:                   3
% 2.40/1.01  comparisons_done:                       0
% 2.40/1.01  comparisons_avoided:                    2
% 2.40/1.01  
% 2.40/1.01  ------ Simplifications
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  sim_fw_subset_subsumed:                 3
% 2.40/1.01  sim_bw_subset_subsumed:                 3
% 2.40/1.01  sim_fw_subsumed:                        8
% 2.40/1.01  sim_bw_subsumed:                        2
% 2.40/1.01  sim_fw_subsumption_res:                 0
% 2.40/1.01  sim_bw_subsumption_res:                 0
% 2.40/1.01  sim_tautology_del:                      1
% 2.40/1.01  sim_eq_tautology_del:                   5
% 2.40/1.01  sim_eq_res_simp:                        0
% 2.40/1.01  sim_fw_demodulated:                     15
% 2.40/1.01  sim_bw_demodulated:                     14
% 2.40/1.01  sim_light_normalised:                   34
% 2.40/1.01  sim_joinable_taut:                      0
% 2.40/1.01  sim_joinable_simp:                      0
% 2.40/1.01  sim_ac_normalised:                      0
% 2.40/1.01  sim_smt_subsumption:                    0
% 2.40/1.01  
%------------------------------------------------------------------------------
