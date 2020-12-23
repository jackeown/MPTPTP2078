%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:10 EST 2020

% Result     : Theorem 8.04s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 828 expanded)
%              Number of clauses        :   40 ( 115 expanded)
%              Number of leaves         :   17 ( 264 expanded)
%              Depth                    :   13
%              Number of atoms          :  143 ( 905 expanded)
%              Number of equality atoms :   89 ( 821 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).

fof(f45,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f35,f29])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f47,f49])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f49,f49])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f30,f47])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f32,f47,f47,f29])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f33,f29,f29,f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f46,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f60,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(definition_unfolding,[],[f46,f47,f50])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_323,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_326,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_328,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2215,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_326,c_328])).

cnf(c_37001,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,X0)
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_323,c_2215])).

cnf(c_37038,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_323,c_37001])).

cnf(c_9,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_37320,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_37038,c_9])).

cnf(c_8,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_737,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_741,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_3])).

cnf(c_2239,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_737,c_741])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2666,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2239,c_5])).

cnf(c_2672,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2666,c_2239])).

cnf(c_2674,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_2672,c_2239])).

cnf(c_7,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_327,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_519,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_327,c_328])).

cnf(c_1106,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_519])).

cnf(c_1387,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1106,c_3])).

cnf(c_938,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_741])).

cnf(c_1395,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1387,c_938])).

cnf(c_2679,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_2674,c_1395])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2662,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2239,c_6])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_329,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_518,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_329,c_328])).

cnf(c_1384,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_938,c_1106])).

cnf(c_2682,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2662,c_518,c_1384])).

cnf(c_2683,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2682,c_2674])).

cnf(c_37326,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_37320,c_2679,c_2683])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2221,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_737,c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37326,c_2221])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 8.04/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.04/1.51  
% 8.04/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.04/1.51  
% 8.04/1.51  ------  iProver source info
% 8.04/1.51  
% 8.04/1.51  git: date: 2020-06-30 10:37:57 +0100
% 8.04/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.04/1.51  git: non_committed_changes: false
% 8.04/1.51  git: last_make_outside_of_git: false
% 8.04/1.51  
% 8.04/1.51  ------ 
% 8.04/1.51  
% 8.04/1.51  ------ Input Options
% 8.04/1.51  
% 8.04/1.51  --out_options                           all
% 8.04/1.51  --tptp_safe_out                         true
% 8.04/1.51  --problem_path                          ""
% 8.04/1.51  --include_path                          ""
% 8.04/1.51  --clausifier                            res/vclausify_rel
% 8.04/1.51  --clausifier_options                    ""
% 8.04/1.51  --stdin                                 false
% 8.04/1.51  --stats_out                             all
% 8.04/1.51  
% 8.04/1.51  ------ General Options
% 8.04/1.51  
% 8.04/1.51  --fof                                   false
% 8.04/1.51  --time_out_real                         305.
% 8.04/1.51  --time_out_virtual                      -1.
% 8.04/1.51  --symbol_type_check                     false
% 8.04/1.51  --clausify_out                          false
% 8.04/1.51  --sig_cnt_out                           false
% 8.04/1.51  --trig_cnt_out                          false
% 8.04/1.51  --trig_cnt_out_tolerance                1.
% 8.04/1.51  --trig_cnt_out_sk_spl                   false
% 8.04/1.51  --abstr_cl_out                          false
% 8.04/1.51  
% 8.04/1.51  ------ Global Options
% 8.04/1.51  
% 8.04/1.51  --schedule                              default
% 8.04/1.51  --add_important_lit                     false
% 8.04/1.51  --prop_solver_per_cl                    1000
% 8.04/1.51  --min_unsat_core                        false
% 8.04/1.51  --soft_assumptions                      false
% 8.04/1.51  --soft_lemma_size                       3
% 8.04/1.51  --prop_impl_unit_size                   0
% 8.04/1.51  --prop_impl_unit                        []
% 8.04/1.51  --share_sel_clauses                     true
% 8.04/1.51  --reset_solvers                         false
% 8.04/1.51  --bc_imp_inh                            [conj_cone]
% 8.04/1.51  --conj_cone_tolerance                   3.
% 8.04/1.51  --extra_neg_conj                        none
% 8.04/1.51  --large_theory_mode                     true
% 8.04/1.51  --prolific_symb_bound                   200
% 8.04/1.51  --lt_threshold                          2000
% 8.04/1.51  --clause_weak_htbl                      true
% 8.04/1.51  --gc_record_bc_elim                     false
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing Options
% 8.04/1.51  
% 8.04/1.51  --preprocessing_flag                    true
% 8.04/1.51  --time_out_prep_mult                    0.1
% 8.04/1.51  --splitting_mode                        input
% 8.04/1.51  --splitting_grd                         true
% 8.04/1.51  --splitting_cvd                         false
% 8.04/1.51  --splitting_cvd_svl                     false
% 8.04/1.51  --splitting_nvd                         32
% 8.04/1.51  --sub_typing                            true
% 8.04/1.51  --prep_gs_sim                           true
% 8.04/1.51  --prep_unflatten                        true
% 8.04/1.51  --prep_res_sim                          true
% 8.04/1.51  --prep_upred                            true
% 8.04/1.51  --prep_sem_filter                       exhaustive
% 8.04/1.51  --prep_sem_filter_out                   false
% 8.04/1.51  --pred_elim                             true
% 8.04/1.51  --res_sim_input                         true
% 8.04/1.51  --eq_ax_congr_red                       true
% 8.04/1.51  --pure_diseq_elim                       true
% 8.04/1.51  --brand_transform                       false
% 8.04/1.51  --non_eq_to_eq                          false
% 8.04/1.51  --prep_def_merge                        true
% 8.04/1.51  --prep_def_merge_prop_impl              false
% 8.04/1.51  --prep_def_merge_mbd                    true
% 8.04/1.51  --prep_def_merge_tr_red                 false
% 8.04/1.51  --prep_def_merge_tr_cl                  false
% 8.04/1.51  --smt_preprocessing                     true
% 8.04/1.51  --smt_ac_axioms                         fast
% 8.04/1.51  --preprocessed_out                      false
% 8.04/1.51  --preprocessed_stats                    false
% 8.04/1.51  
% 8.04/1.51  ------ Abstraction refinement Options
% 8.04/1.51  
% 8.04/1.51  --abstr_ref                             []
% 8.04/1.51  --abstr_ref_prep                        false
% 8.04/1.51  --abstr_ref_until_sat                   false
% 8.04/1.51  --abstr_ref_sig_restrict                funpre
% 8.04/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 8.04/1.51  --abstr_ref_under                       []
% 8.04/1.51  
% 8.04/1.51  ------ SAT Options
% 8.04/1.51  
% 8.04/1.51  --sat_mode                              false
% 8.04/1.51  --sat_fm_restart_options                ""
% 8.04/1.51  --sat_gr_def                            false
% 8.04/1.51  --sat_epr_types                         true
% 8.04/1.51  --sat_non_cyclic_types                  false
% 8.04/1.51  --sat_finite_models                     false
% 8.04/1.51  --sat_fm_lemmas                         false
% 8.04/1.51  --sat_fm_prep                           false
% 8.04/1.51  --sat_fm_uc_incr                        true
% 8.04/1.51  --sat_out_model                         small
% 8.04/1.51  --sat_out_clauses                       false
% 8.04/1.51  
% 8.04/1.51  ------ QBF Options
% 8.04/1.51  
% 8.04/1.51  --qbf_mode                              false
% 8.04/1.51  --qbf_elim_univ                         false
% 8.04/1.51  --qbf_dom_inst                          none
% 8.04/1.51  --qbf_dom_pre_inst                      false
% 8.04/1.51  --qbf_sk_in                             false
% 8.04/1.51  --qbf_pred_elim                         true
% 8.04/1.51  --qbf_split                             512
% 8.04/1.51  
% 8.04/1.51  ------ BMC1 Options
% 8.04/1.51  
% 8.04/1.51  --bmc1_incremental                      false
% 8.04/1.51  --bmc1_axioms                           reachable_all
% 8.04/1.51  --bmc1_min_bound                        0
% 8.04/1.51  --bmc1_max_bound                        -1
% 8.04/1.51  --bmc1_max_bound_default                -1
% 8.04/1.51  --bmc1_symbol_reachability              true
% 8.04/1.51  --bmc1_property_lemmas                  false
% 8.04/1.51  --bmc1_k_induction                      false
% 8.04/1.51  --bmc1_non_equiv_states                 false
% 8.04/1.51  --bmc1_deadlock                         false
% 8.04/1.51  --bmc1_ucm                              false
% 8.04/1.51  --bmc1_add_unsat_core                   none
% 8.04/1.51  --bmc1_unsat_core_children              false
% 8.04/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 8.04/1.51  --bmc1_out_stat                         full
% 8.04/1.51  --bmc1_ground_init                      false
% 8.04/1.51  --bmc1_pre_inst_next_state              false
% 8.04/1.51  --bmc1_pre_inst_state                   false
% 8.04/1.51  --bmc1_pre_inst_reach_state             false
% 8.04/1.51  --bmc1_out_unsat_core                   false
% 8.04/1.51  --bmc1_aig_witness_out                  false
% 8.04/1.51  --bmc1_verbose                          false
% 8.04/1.51  --bmc1_dump_clauses_tptp                false
% 8.04/1.51  --bmc1_dump_unsat_core_tptp             false
% 8.04/1.51  --bmc1_dump_file                        -
% 8.04/1.51  --bmc1_ucm_expand_uc_limit              128
% 8.04/1.51  --bmc1_ucm_n_expand_iterations          6
% 8.04/1.51  --bmc1_ucm_extend_mode                  1
% 8.04/1.51  --bmc1_ucm_init_mode                    2
% 8.04/1.51  --bmc1_ucm_cone_mode                    none
% 8.04/1.51  --bmc1_ucm_reduced_relation_type        0
% 8.04/1.51  --bmc1_ucm_relax_model                  4
% 8.04/1.51  --bmc1_ucm_full_tr_after_sat            true
% 8.04/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 8.04/1.51  --bmc1_ucm_layered_model                none
% 8.04/1.51  --bmc1_ucm_max_lemma_size               10
% 8.04/1.51  
% 8.04/1.51  ------ AIG Options
% 8.04/1.51  
% 8.04/1.51  --aig_mode                              false
% 8.04/1.51  
% 8.04/1.51  ------ Instantiation Options
% 8.04/1.51  
% 8.04/1.51  --instantiation_flag                    true
% 8.04/1.51  --inst_sos_flag                         true
% 8.04/1.51  --inst_sos_phase                        true
% 8.04/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.04/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.04/1.51  --inst_lit_sel_side                     num_symb
% 8.04/1.51  --inst_solver_per_active                1400
% 8.04/1.51  --inst_solver_calls_frac                1.
% 8.04/1.51  --inst_passive_queue_type               priority_queues
% 8.04/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.04/1.51  --inst_passive_queues_freq              [25;2]
% 8.04/1.51  --inst_dismatching                      true
% 8.04/1.51  --inst_eager_unprocessed_to_passive     true
% 8.04/1.51  --inst_prop_sim_given                   true
% 8.04/1.51  --inst_prop_sim_new                     false
% 8.04/1.51  --inst_subs_new                         false
% 8.04/1.51  --inst_eq_res_simp                      false
% 8.04/1.51  --inst_subs_given                       false
% 8.04/1.51  --inst_orphan_elimination               true
% 8.04/1.51  --inst_learning_loop_flag               true
% 8.04/1.51  --inst_learning_start                   3000
% 8.04/1.51  --inst_learning_factor                  2
% 8.04/1.51  --inst_start_prop_sim_after_learn       3
% 8.04/1.51  --inst_sel_renew                        solver
% 8.04/1.51  --inst_lit_activity_flag                true
% 8.04/1.51  --inst_restr_to_given                   false
% 8.04/1.51  --inst_activity_threshold               500
% 8.04/1.51  --inst_out_proof                        true
% 8.04/1.51  
% 8.04/1.51  ------ Resolution Options
% 8.04/1.51  
% 8.04/1.51  --resolution_flag                       true
% 8.04/1.51  --res_lit_sel                           adaptive
% 8.04/1.51  --res_lit_sel_side                      none
% 8.04/1.51  --res_ordering                          kbo
% 8.04/1.51  --res_to_prop_solver                    active
% 8.04/1.51  --res_prop_simpl_new                    false
% 8.04/1.51  --res_prop_simpl_given                  true
% 8.04/1.51  --res_passive_queue_type                priority_queues
% 8.04/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.04/1.51  --res_passive_queues_freq               [15;5]
% 8.04/1.51  --res_forward_subs                      full
% 8.04/1.51  --res_backward_subs                     full
% 8.04/1.51  --res_forward_subs_resolution           true
% 8.04/1.51  --res_backward_subs_resolution          true
% 8.04/1.51  --res_orphan_elimination                true
% 8.04/1.51  --res_time_limit                        2.
% 8.04/1.51  --res_out_proof                         true
% 8.04/1.51  
% 8.04/1.51  ------ Superposition Options
% 8.04/1.51  
% 8.04/1.51  --superposition_flag                    true
% 8.04/1.51  --sup_passive_queue_type                priority_queues
% 8.04/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.04/1.51  --sup_passive_queues_freq               [8;1;4]
% 8.04/1.51  --demod_completeness_check              fast
% 8.04/1.51  --demod_use_ground                      true
% 8.04/1.51  --sup_to_prop_solver                    passive
% 8.04/1.51  --sup_prop_simpl_new                    true
% 8.04/1.51  --sup_prop_simpl_given                  true
% 8.04/1.51  --sup_fun_splitting                     true
% 8.04/1.51  --sup_smt_interval                      50000
% 8.04/1.51  
% 8.04/1.51  ------ Superposition Simplification Setup
% 8.04/1.51  
% 8.04/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.04/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.04/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.04/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 8.04/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.04/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.04/1.51  --sup_immed_triv                        [TrivRules]
% 8.04/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.51  --sup_immed_bw_main                     []
% 8.04/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.04/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 8.04/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.51  --sup_input_bw                          []
% 8.04/1.51  
% 8.04/1.51  ------ Combination Options
% 8.04/1.51  
% 8.04/1.51  --comb_res_mult                         3
% 8.04/1.51  --comb_sup_mult                         2
% 8.04/1.51  --comb_inst_mult                        10
% 8.04/1.51  
% 8.04/1.51  ------ Debug Options
% 8.04/1.51  
% 8.04/1.51  --dbg_backtrace                         false
% 8.04/1.51  --dbg_dump_prop_clauses                 false
% 8.04/1.51  --dbg_dump_prop_clauses_file            -
% 8.04/1.51  --dbg_out_stat                          false
% 8.04/1.51  ------ Parsing...
% 8.04/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.04/1.51  ------ Proving...
% 8.04/1.51  ------ Problem Properties 
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  clauses                                 14
% 8.04/1.51  conjectures                             2
% 8.04/1.51  EPR                                     3
% 8.04/1.51  Horn                                    14
% 8.04/1.51  unary                                   9
% 8.04/1.51  binary                                  3
% 8.04/1.51  lits                                    21
% 8.04/1.51  lits eq                                 8
% 8.04/1.51  fd_pure                                 0
% 8.04/1.51  fd_pseudo                               0
% 8.04/1.51  fd_cond                                 0
% 8.04/1.51  fd_pseudo_cond                          1
% 8.04/1.51  AC symbols                              0
% 8.04/1.51  
% 8.04/1.51  ------ Schedule dynamic 5 is on 
% 8.04/1.51  
% 8.04/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  ------ 
% 8.04/1.51  Current options:
% 8.04/1.51  ------ 
% 8.04/1.51  
% 8.04/1.51  ------ Input Options
% 8.04/1.51  
% 8.04/1.51  --out_options                           all
% 8.04/1.51  --tptp_safe_out                         true
% 8.04/1.51  --problem_path                          ""
% 8.04/1.51  --include_path                          ""
% 8.04/1.51  --clausifier                            res/vclausify_rel
% 8.04/1.51  --clausifier_options                    ""
% 8.04/1.51  --stdin                                 false
% 8.04/1.51  --stats_out                             all
% 8.04/1.51  
% 8.04/1.51  ------ General Options
% 8.04/1.51  
% 8.04/1.51  --fof                                   false
% 8.04/1.51  --time_out_real                         305.
% 8.04/1.51  --time_out_virtual                      -1.
% 8.04/1.51  --symbol_type_check                     false
% 8.04/1.51  --clausify_out                          false
% 8.04/1.51  --sig_cnt_out                           false
% 8.04/1.51  --trig_cnt_out                          false
% 8.04/1.51  --trig_cnt_out_tolerance                1.
% 8.04/1.51  --trig_cnt_out_sk_spl                   false
% 8.04/1.51  --abstr_cl_out                          false
% 8.04/1.51  
% 8.04/1.51  ------ Global Options
% 8.04/1.51  
% 8.04/1.51  --schedule                              default
% 8.04/1.51  --add_important_lit                     false
% 8.04/1.51  --prop_solver_per_cl                    1000
% 8.04/1.51  --min_unsat_core                        false
% 8.04/1.51  --soft_assumptions                      false
% 8.04/1.51  --soft_lemma_size                       3
% 8.04/1.51  --prop_impl_unit_size                   0
% 8.04/1.51  --prop_impl_unit                        []
% 8.04/1.51  --share_sel_clauses                     true
% 8.04/1.51  --reset_solvers                         false
% 8.04/1.51  --bc_imp_inh                            [conj_cone]
% 8.04/1.51  --conj_cone_tolerance                   3.
% 8.04/1.51  --extra_neg_conj                        none
% 8.04/1.51  --large_theory_mode                     true
% 8.04/1.51  --prolific_symb_bound                   200
% 8.04/1.51  --lt_threshold                          2000
% 8.04/1.51  --clause_weak_htbl                      true
% 8.04/1.51  --gc_record_bc_elim                     false
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing Options
% 8.04/1.51  
% 8.04/1.51  --preprocessing_flag                    true
% 8.04/1.51  --time_out_prep_mult                    0.1
% 8.04/1.51  --splitting_mode                        input
% 8.04/1.51  --splitting_grd                         true
% 8.04/1.51  --splitting_cvd                         false
% 8.04/1.51  --splitting_cvd_svl                     false
% 8.04/1.51  --splitting_nvd                         32
% 8.04/1.51  --sub_typing                            true
% 8.04/1.51  --prep_gs_sim                           true
% 8.04/1.51  --prep_unflatten                        true
% 8.04/1.51  --prep_res_sim                          true
% 8.04/1.51  --prep_upred                            true
% 8.04/1.51  --prep_sem_filter                       exhaustive
% 8.04/1.51  --prep_sem_filter_out                   false
% 8.04/1.51  --pred_elim                             true
% 8.04/1.51  --res_sim_input                         true
% 8.04/1.51  --eq_ax_congr_red                       true
% 8.04/1.51  --pure_diseq_elim                       true
% 8.04/1.51  --brand_transform                       false
% 8.04/1.51  --non_eq_to_eq                          false
% 8.04/1.51  --prep_def_merge                        true
% 8.04/1.51  --prep_def_merge_prop_impl              false
% 8.04/1.51  --prep_def_merge_mbd                    true
% 8.04/1.51  --prep_def_merge_tr_red                 false
% 8.04/1.51  --prep_def_merge_tr_cl                  false
% 8.04/1.51  --smt_preprocessing                     true
% 8.04/1.51  --smt_ac_axioms                         fast
% 8.04/1.51  --preprocessed_out                      false
% 8.04/1.51  --preprocessed_stats                    false
% 8.04/1.51  
% 8.04/1.51  ------ Abstraction refinement Options
% 8.04/1.51  
% 8.04/1.51  --abstr_ref                             []
% 8.04/1.51  --abstr_ref_prep                        false
% 8.04/1.51  --abstr_ref_until_sat                   false
% 8.04/1.51  --abstr_ref_sig_restrict                funpre
% 8.04/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 8.04/1.51  --abstr_ref_under                       []
% 8.04/1.51  
% 8.04/1.51  ------ SAT Options
% 8.04/1.51  
% 8.04/1.51  --sat_mode                              false
% 8.04/1.51  --sat_fm_restart_options                ""
% 8.04/1.51  --sat_gr_def                            false
% 8.04/1.51  --sat_epr_types                         true
% 8.04/1.51  --sat_non_cyclic_types                  false
% 8.04/1.51  --sat_finite_models                     false
% 8.04/1.51  --sat_fm_lemmas                         false
% 8.04/1.51  --sat_fm_prep                           false
% 8.04/1.51  --sat_fm_uc_incr                        true
% 8.04/1.51  --sat_out_model                         small
% 8.04/1.51  --sat_out_clauses                       false
% 8.04/1.51  
% 8.04/1.51  ------ QBF Options
% 8.04/1.51  
% 8.04/1.51  --qbf_mode                              false
% 8.04/1.51  --qbf_elim_univ                         false
% 8.04/1.51  --qbf_dom_inst                          none
% 8.04/1.51  --qbf_dom_pre_inst                      false
% 8.04/1.51  --qbf_sk_in                             false
% 8.04/1.51  --qbf_pred_elim                         true
% 8.04/1.51  --qbf_split                             512
% 8.04/1.51  
% 8.04/1.51  ------ BMC1 Options
% 8.04/1.51  
% 8.04/1.51  --bmc1_incremental                      false
% 8.04/1.51  --bmc1_axioms                           reachable_all
% 8.04/1.51  --bmc1_min_bound                        0
% 8.04/1.51  --bmc1_max_bound                        -1
% 8.04/1.51  --bmc1_max_bound_default                -1
% 8.04/1.51  --bmc1_symbol_reachability              true
% 8.04/1.51  --bmc1_property_lemmas                  false
% 8.04/1.51  --bmc1_k_induction                      false
% 8.04/1.51  --bmc1_non_equiv_states                 false
% 8.04/1.51  --bmc1_deadlock                         false
% 8.04/1.51  --bmc1_ucm                              false
% 8.04/1.51  --bmc1_add_unsat_core                   none
% 8.04/1.51  --bmc1_unsat_core_children              false
% 8.04/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 8.04/1.51  --bmc1_out_stat                         full
% 8.04/1.51  --bmc1_ground_init                      false
% 8.04/1.51  --bmc1_pre_inst_next_state              false
% 8.04/1.51  --bmc1_pre_inst_state                   false
% 8.04/1.51  --bmc1_pre_inst_reach_state             false
% 8.04/1.51  --bmc1_out_unsat_core                   false
% 8.04/1.51  --bmc1_aig_witness_out                  false
% 8.04/1.51  --bmc1_verbose                          false
% 8.04/1.51  --bmc1_dump_clauses_tptp                false
% 8.04/1.51  --bmc1_dump_unsat_core_tptp             false
% 8.04/1.51  --bmc1_dump_file                        -
% 8.04/1.51  --bmc1_ucm_expand_uc_limit              128
% 8.04/1.51  --bmc1_ucm_n_expand_iterations          6
% 8.04/1.51  --bmc1_ucm_extend_mode                  1
% 8.04/1.51  --bmc1_ucm_init_mode                    2
% 8.04/1.51  --bmc1_ucm_cone_mode                    none
% 8.04/1.51  --bmc1_ucm_reduced_relation_type        0
% 8.04/1.51  --bmc1_ucm_relax_model                  4
% 8.04/1.51  --bmc1_ucm_full_tr_after_sat            true
% 8.04/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 8.04/1.51  --bmc1_ucm_layered_model                none
% 8.04/1.51  --bmc1_ucm_max_lemma_size               10
% 8.04/1.51  
% 8.04/1.51  ------ AIG Options
% 8.04/1.51  
% 8.04/1.51  --aig_mode                              false
% 8.04/1.51  
% 8.04/1.51  ------ Instantiation Options
% 8.04/1.51  
% 8.04/1.51  --instantiation_flag                    true
% 8.04/1.51  --inst_sos_flag                         true
% 8.04/1.51  --inst_sos_phase                        true
% 8.04/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.04/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.04/1.51  --inst_lit_sel_side                     none
% 8.04/1.51  --inst_solver_per_active                1400
% 8.04/1.51  --inst_solver_calls_frac                1.
% 8.04/1.51  --inst_passive_queue_type               priority_queues
% 8.04/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.04/1.51  --inst_passive_queues_freq              [25;2]
% 8.04/1.51  --inst_dismatching                      true
% 8.04/1.51  --inst_eager_unprocessed_to_passive     true
% 8.04/1.51  --inst_prop_sim_given                   true
% 8.04/1.51  --inst_prop_sim_new                     false
% 8.04/1.51  --inst_subs_new                         false
% 8.04/1.51  --inst_eq_res_simp                      false
% 8.04/1.51  --inst_subs_given                       false
% 8.04/1.51  --inst_orphan_elimination               true
% 8.04/1.51  --inst_learning_loop_flag               true
% 8.04/1.51  --inst_learning_start                   3000
% 8.04/1.51  --inst_learning_factor                  2
% 8.04/1.51  --inst_start_prop_sim_after_learn       3
% 8.04/1.51  --inst_sel_renew                        solver
% 8.04/1.51  --inst_lit_activity_flag                true
% 8.04/1.51  --inst_restr_to_given                   false
% 8.04/1.51  --inst_activity_threshold               500
% 8.04/1.51  --inst_out_proof                        true
% 8.04/1.51  
% 8.04/1.51  ------ Resolution Options
% 8.04/1.51  
% 8.04/1.51  --resolution_flag                       false
% 8.04/1.51  --res_lit_sel                           adaptive
% 8.04/1.51  --res_lit_sel_side                      none
% 8.04/1.51  --res_ordering                          kbo
% 8.04/1.51  --res_to_prop_solver                    active
% 8.04/1.51  --res_prop_simpl_new                    false
% 8.04/1.51  --res_prop_simpl_given                  true
% 8.04/1.51  --res_passive_queue_type                priority_queues
% 8.04/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.04/1.51  --res_passive_queues_freq               [15;5]
% 8.04/1.51  --res_forward_subs                      full
% 8.04/1.51  --res_backward_subs                     full
% 8.04/1.51  --res_forward_subs_resolution           true
% 8.04/1.51  --res_backward_subs_resolution          true
% 8.04/1.51  --res_orphan_elimination                true
% 8.04/1.51  --res_time_limit                        2.
% 8.04/1.51  --res_out_proof                         true
% 8.04/1.51  
% 8.04/1.51  ------ Superposition Options
% 8.04/1.51  
% 8.04/1.51  --superposition_flag                    true
% 8.04/1.51  --sup_passive_queue_type                priority_queues
% 8.04/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.04/1.51  --sup_passive_queues_freq               [8;1;4]
% 8.04/1.51  --demod_completeness_check              fast
% 8.04/1.51  --demod_use_ground                      true
% 8.04/1.51  --sup_to_prop_solver                    passive
% 8.04/1.51  --sup_prop_simpl_new                    true
% 8.04/1.51  --sup_prop_simpl_given                  true
% 8.04/1.51  --sup_fun_splitting                     true
% 8.04/1.51  --sup_smt_interval                      50000
% 8.04/1.51  
% 8.04/1.51  ------ Superposition Simplification Setup
% 8.04/1.51  
% 8.04/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.04/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.04/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.04/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 8.04/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.04/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.04/1.51  --sup_immed_triv                        [TrivRules]
% 8.04/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.51  --sup_immed_bw_main                     []
% 8.04/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.04/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 8.04/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.51  --sup_input_bw                          []
% 8.04/1.51  
% 8.04/1.51  ------ Combination Options
% 8.04/1.51  
% 8.04/1.51  --comb_res_mult                         3
% 8.04/1.51  --comb_sup_mult                         2
% 8.04/1.51  --comb_inst_mult                        10
% 8.04/1.51  
% 8.04/1.51  ------ Debug Options
% 8.04/1.51  
% 8.04/1.51  --dbg_backtrace                         false
% 8.04/1.51  --dbg_dump_prop_clauses                 false
% 8.04/1.51  --dbg_dump_prop_clauses_file            -
% 8.04/1.51  --dbg_out_stat                          false
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  ------ Proving...
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  % SZS status Theorem for theBenchmark.p
% 8.04/1.51  
% 8.04/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 8.04/1.51  
% 8.04/1.51  fof(f16,conjecture,(
% 8.04/1.51    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f17,negated_conjecture,(
% 8.04/1.51    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 8.04/1.51    inference(negated_conjecture,[],[f16])).
% 8.04/1.51  
% 8.04/1.51  fof(f19,plain,(
% 8.04/1.51    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 8.04/1.51    inference(ennf_transformation,[],[f17])).
% 8.04/1.51  
% 8.04/1.51  fof(f24,plain,(
% 8.04/1.51    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1))),
% 8.04/1.51    introduced(choice_axiom,[])).
% 8.04/1.51  
% 8.04/1.51  fof(f25,plain,(
% 8.04/1.51    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1)),
% 8.04/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).
% 8.04/1.51  
% 8.04/1.51  fof(f45,plain,(
% 8.04/1.51    r2_hidden(sK0,sK1)),
% 8.04/1.51    inference(cnf_transformation,[],[f25])).
% 8.04/1.51  
% 8.04/1.51  fof(f15,axiom,(
% 8.04/1.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f22,plain,(
% 8.04/1.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 8.04/1.51    inference(nnf_transformation,[],[f15])).
% 8.04/1.51  
% 8.04/1.51  fof(f23,plain,(
% 8.04/1.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 8.04/1.51    inference(flattening,[],[f22])).
% 8.04/1.51  
% 8.04/1.51  fof(f44,plain,(
% 8.04/1.51    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f23])).
% 8.04/1.51  
% 8.04/1.51  fof(f11,axiom,(
% 8.04/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f38,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f11])).
% 8.04/1.51  
% 8.04/1.51  fof(f12,axiom,(
% 8.04/1.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f39,plain,(
% 8.04/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f12])).
% 8.04/1.51  
% 8.04/1.51  fof(f13,axiom,(
% 8.04/1.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f40,plain,(
% 8.04/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f13])).
% 8.04/1.51  
% 8.04/1.51  fof(f48,plain,(
% 8.04/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 8.04/1.51    inference(definition_unfolding,[],[f39,f40])).
% 8.04/1.51  
% 8.04/1.51  fof(f49,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 8.04/1.51    inference(definition_unfolding,[],[f38,f48])).
% 8.04/1.51  
% 8.04/1.51  fof(f57,plain,(
% 8.04/1.51    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 8.04/1.51    inference(definition_unfolding,[],[f44,f49])).
% 8.04/1.51  
% 8.04/1.51  fof(f4,axiom,(
% 8.04/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f18,plain,(
% 8.04/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 8.04/1.51    inference(ennf_transformation,[],[f4])).
% 8.04/1.51  
% 8.04/1.51  fof(f31,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f18])).
% 8.04/1.51  
% 8.04/1.51  fof(f14,axiom,(
% 8.04/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f41,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f14])).
% 8.04/1.51  
% 8.04/1.51  fof(f8,axiom,(
% 8.04/1.51    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f35,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f8])).
% 8.04/1.51  
% 8.04/1.51  fof(f2,axiom,(
% 8.04/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f29,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f2])).
% 8.04/1.51  
% 8.04/1.51  fof(f47,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 8.04/1.51    inference(definition_unfolding,[],[f35,f29])).
% 8.04/1.51  
% 8.04/1.51  fof(f56,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 8.04/1.51    inference(definition_unfolding,[],[f41,f47,f49])).
% 8.04/1.51  
% 8.04/1.51  fof(f9,axiom,(
% 8.04/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f36,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f9])).
% 8.04/1.51  
% 8.04/1.51  fof(f55,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 8.04/1.51    inference(definition_unfolding,[],[f36,f49,f49])).
% 8.04/1.51  
% 8.04/1.51  fof(f3,axiom,(
% 8.04/1.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f30,plain,(
% 8.04/1.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.04/1.51    inference(cnf_transformation,[],[f3])).
% 8.04/1.51  
% 8.04/1.51  fof(f51,plain,(
% 8.04/1.51    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 8.04/1.51    inference(definition_unfolding,[],[f30,f47])).
% 8.04/1.51  
% 8.04/1.51  fof(f5,axiom,(
% 8.04/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f32,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f5])).
% 8.04/1.51  
% 8.04/1.51  fof(f52,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 8.04/1.51    inference(definition_unfolding,[],[f32,f47,f47,f29])).
% 8.04/1.51  
% 8.04/1.51  fof(f7,axiom,(
% 8.04/1.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f34,plain,(
% 8.04/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f7])).
% 8.04/1.51  
% 8.04/1.51  fof(f54,plain,(
% 8.04/1.51    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 8.04/1.51    inference(definition_unfolding,[],[f34,f47])).
% 8.04/1.51  
% 8.04/1.51  fof(f6,axiom,(
% 8.04/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f33,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f6])).
% 8.04/1.51  
% 8.04/1.51  fof(f53,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 8.04/1.51    inference(definition_unfolding,[],[f33,f29,f29,f47])).
% 8.04/1.51  
% 8.04/1.51  fof(f1,axiom,(
% 8.04/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f20,plain,(
% 8.04/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.04/1.51    inference(nnf_transformation,[],[f1])).
% 8.04/1.51  
% 8.04/1.51  fof(f21,plain,(
% 8.04/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.04/1.51    inference(flattening,[],[f20])).
% 8.04/1.51  
% 8.04/1.51  fof(f26,plain,(
% 8.04/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 8.04/1.51    inference(cnf_transformation,[],[f21])).
% 8.04/1.51  
% 8.04/1.51  fof(f62,plain,(
% 8.04/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.04/1.51    inference(equality_resolution,[],[f26])).
% 8.04/1.51  
% 8.04/1.51  fof(f46,plain,(
% 8.04/1.51    k2_xboole_0(k1_tarski(sK0),sK1) != sK1),
% 8.04/1.51    inference(cnf_transformation,[],[f25])).
% 8.04/1.51  
% 8.04/1.51  fof(f10,axiom,(
% 8.04/1.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f37,plain,(
% 8.04/1.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f10])).
% 8.04/1.51  
% 8.04/1.51  fof(f50,plain,(
% 8.04/1.51    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 8.04/1.51    inference(definition_unfolding,[],[f37,f49])).
% 8.04/1.51  
% 8.04/1.51  fof(f60,plain,(
% 8.04/1.51    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1),
% 8.04/1.51    inference(definition_unfolding,[],[f46,f47,f50])).
% 8.04/1.51  
% 8.04/1.51  cnf(c_14,negated_conjecture,
% 8.04/1.51      ( r2_hidden(sK0,sK1) ),
% 8.04/1.51      inference(cnf_transformation,[],[f45]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_323,plain,
% 8.04/1.51      ( r2_hidden(sK0,sK1) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_10,plain,
% 8.04/1.51      ( ~ r2_hidden(X0,X1)
% 8.04/1.51      | ~ r2_hidden(X2,X1)
% 8.04/1.51      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
% 8.04/1.51      inference(cnf_transformation,[],[f57]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_326,plain,
% 8.04/1.51      ( r2_hidden(X0,X1) != iProver_top
% 8.04/1.51      | r2_hidden(X2,X1) != iProver_top
% 8.04/1.51      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_4,plain,
% 8.04/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 8.04/1.51      inference(cnf_transformation,[],[f31]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_328,plain,
% 8.04/1.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2215,plain,
% 8.04/1.51      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 8.04/1.51      | r2_hidden(X1,X2) != iProver_top
% 8.04/1.51      | r2_hidden(X0,X2) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_326,c_328]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_37001,plain,
% 8.04/1.51      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,X0)
% 8.04/1.51      | r2_hidden(X0,sK1) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_323,c_2215]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_37038,plain,
% 8.04/1.51      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_323,c_37001]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_9,plain,
% 8.04/1.51      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 8.04/1.51      inference(cnf_transformation,[],[f56]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_37320,plain,
% 8.04/1.51      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_37038,c_9]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_8,plain,
% 8.04/1.51      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 8.04/1.51      inference(cnf_transformation,[],[f55]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_737,plain,
% 8.04/1.51      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_3,plain,
% 8.04/1.51      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 8.04/1.51      inference(cnf_transformation,[],[f51]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_741,plain,
% 8.04/1.51      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_9,c_3]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2239,plain,
% 8.04/1.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_737,c_741]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_5,plain,
% 8.04/1.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 8.04/1.51      inference(cnf_transformation,[],[f52]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2666,plain,
% 8.04/1.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_2239,c_5]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2672,plain,
% 8.04/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_2666,c_2239]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2674,plain,
% 8.04/1.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_2672,c_2239]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_7,plain,
% 8.04/1.51      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 8.04/1.51      inference(cnf_transformation,[],[f54]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_327,plain,
% 8.04/1.51      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_519,plain,
% 8.04/1.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_327,c_328]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1106,plain,
% 8.04/1.51      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_9,c_519]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1387,plain,
% 8.04/1.51      ( k5_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_1106,c_3]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_938,plain,
% 8.04/1.51      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_8,c_741]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1395,plain,
% 8.04/1.51      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
% 8.04/1.51      inference(light_normalisation,[status(thm)],[c_1387,c_938]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2679,plain,
% 8.04/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_2674,c_1395]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_6,plain,
% 8.04/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 8.04/1.51      inference(cnf_transformation,[],[f53]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2662,plain,
% 8.04/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_2239,c_6]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2,plain,
% 8.04/1.51      ( r1_tarski(X0,X0) ),
% 8.04/1.51      inference(cnf_transformation,[],[f62]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_329,plain,
% 8.04/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_518,plain,
% 8.04/1.51      ( k3_xboole_0(X0,X0) = X0 ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_329,c_328]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1384,plain,
% 8.04/1.51      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_938,c_1106]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2682,plain,
% 8.04/1.51      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 8.04/1.51      inference(light_normalisation,[status(thm)],[c_2662,c_518,c_1384]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2683,plain,
% 8.04/1.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_2682,c_2674]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_37326,plain,
% 8.04/1.51      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_37320,c_2679,c_2683]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_13,negated_conjecture,
% 8.04/1.51      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 8.04/1.51      inference(cnf_transformation,[],[f60]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2221,plain,
% 8.04/1.51      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_737,c_13]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(contradiction,plain,
% 8.04/1.51      ( $false ),
% 8.04/1.51      inference(minisat,[status(thm)],[c_37326,c_2221]) ).
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 8.04/1.51  
% 8.04/1.51  ------                               Statistics
% 8.04/1.51  
% 8.04/1.51  ------ General
% 8.04/1.51  
% 8.04/1.51  abstr_ref_over_cycles:                  0
% 8.04/1.51  abstr_ref_under_cycles:                 0
% 8.04/1.51  gc_basic_clause_elim:                   0
% 8.04/1.51  forced_gc_time:                         0
% 8.04/1.51  parsing_time:                           0.01
% 8.04/1.51  unif_index_cands_time:                  0.
% 8.04/1.51  unif_index_add_time:                    0.
% 8.04/1.51  orderings_time:                         0.
% 8.04/1.51  out_proof_time:                         0.009
% 8.04/1.51  total_time:                             1.002
% 8.04/1.51  num_of_symbols:                         40
% 8.04/1.51  num_of_terms:                           28904
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing
% 8.04/1.51  
% 8.04/1.51  num_of_splits:                          0
% 8.04/1.51  num_of_split_atoms:                     0
% 8.04/1.51  num_of_reused_defs:                     0
% 8.04/1.51  num_eq_ax_congr_red:                    0
% 8.04/1.51  num_of_sem_filtered_clauses:            1
% 8.04/1.51  num_of_subtypes:                        0
% 8.04/1.51  monotx_restored_types:                  0
% 8.04/1.51  sat_num_of_epr_types:                   0
% 8.04/1.51  sat_num_of_non_cyclic_types:            0
% 8.04/1.51  sat_guarded_non_collapsed_types:        0
% 8.04/1.51  num_pure_diseq_elim:                    0
% 8.04/1.51  simp_replaced_by:                       0
% 8.04/1.51  res_preprocessed:                       73
% 8.04/1.51  prep_upred:                             0
% 8.04/1.51  prep_unflattend:                        0
% 8.04/1.51  smt_new_axioms:                         0
% 8.04/1.51  pred_elim_cands:                        2
% 8.04/1.51  pred_elim:                              0
% 8.04/1.51  pred_elim_cl:                           0
% 8.04/1.51  pred_elim_cycles:                       2
% 8.04/1.51  merged_defs:                            0
% 8.04/1.51  merged_defs_ncl:                        0
% 8.04/1.51  bin_hyper_res:                          0
% 8.04/1.51  prep_cycles:                            4
% 8.04/1.51  pred_elim_time:                         0.
% 8.04/1.51  splitting_time:                         0.
% 8.04/1.51  sem_filter_time:                        0.
% 8.04/1.51  monotx_time:                            0.
% 8.04/1.51  subtype_inf_time:                       0.
% 8.04/1.51  
% 8.04/1.51  ------ Problem properties
% 8.04/1.51  
% 8.04/1.51  clauses:                                14
% 8.04/1.51  conjectures:                            2
% 8.04/1.51  epr:                                    3
% 8.04/1.51  horn:                                   14
% 8.04/1.51  ground:                                 2
% 8.04/1.51  unary:                                  9
% 8.04/1.51  binary:                                 3
% 8.04/1.51  lits:                                   21
% 8.04/1.51  lits_eq:                                8
% 8.04/1.51  fd_pure:                                0
% 8.04/1.51  fd_pseudo:                              0
% 8.04/1.51  fd_cond:                                0
% 8.04/1.51  fd_pseudo_cond:                         1
% 8.04/1.51  ac_symbols:                             0
% 8.04/1.51  
% 8.04/1.51  ------ Propositional Solver
% 8.04/1.51  
% 8.04/1.51  prop_solver_calls:                      34
% 8.04/1.51  prop_fast_solver_calls:                 549
% 8.04/1.51  smt_solver_calls:                       0
% 8.04/1.51  smt_fast_solver_calls:                  0
% 8.04/1.51  prop_num_of_clauses:                    6344
% 8.04/1.51  prop_preprocess_simplified:             11007
% 8.04/1.51  prop_fo_subsumed:                       0
% 8.04/1.51  prop_solver_time:                       0.
% 8.04/1.51  smt_solver_time:                        0.
% 8.04/1.51  smt_fast_solver_time:                   0.
% 8.04/1.51  prop_fast_solver_time:                  0.
% 8.04/1.51  prop_unsat_core_time:                   0.
% 8.04/1.51  
% 8.04/1.51  ------ QBF
% 8.04/1.51  
% 8.04/1.51  qbf_q_res:                              0
% 8.04/1.51  qbf_num_tautologies:                    0
% 8.04/1.51  qbf_prep_cycles:                        0
% 8.04/1.51  
% 8.04/1.51  ------ BMC1
% 8.04/1.51  
% 8.04/1.51  bmc1_current_bound:                     -1
% 8.04/1.51  bmc1_last_solved_bound:                 -1
% 8.04/1.51  bmc1_unsat_core_size:                   -1
% 8.04/1.51  bmc1_unsat_core_parents_size:           -1
% 8.04/1.51  bmc1_merge_next_fun:                    0
% 8.04/1.51  bmc1_unsat_core_clauses_time:           0.
% 8.04/1.51  
% 8.04/1.51  ------ Instantiation
% 8.04/1.51  
% 8.04/1.51  inst_num_of_clauses:                    2383
% 8.04/1.51  inst_num_in_passive:                    347
% 8.04/1.51  inst_num_in_active:                     838
% 8.04/1.51  inst_num_in_unprocessed:                1198
% 8.04/1.51  inst_num_of_loops:                      910
% 8.04/1.51  inst_num_of_learning_restarts:          0
% 8.04/1.51  inst_num_moves_active_passive:          67
% 8.04/1.51  inst_lit_activity:                      0
% 8.04/1.51  inst_lit_activity_moves:                0
% 8.04/1.51  inst_num_tautologies:                   0
% 8.04/1.51  inst_num_prop_implied:                  0
% 8.04/1.51  inst_num_existing_simplified:           0
% 8.04/1.51  inst_num_eq_res_simplified:             0
% 8.04/1.51  inst_num_child_elim:                    0
% 8.04/1.51  inst_num_of_dismatching_blockings:      846
% 8.04/1.51  inst_num_of_non_proper_insts:           2906
% 8.04/1.51  inst_num_of_duplicates:                 0
% 8.04/1.51  inst_inst_num_from_inst_to_res:         0
% 8.04/1.51  inst_dismatching_checking_time:         0.
% 8.04/1.51  
% 8.04/1.51  ------ Resolution
% 8.04/1.51  
% 8.04/1.51  res_num_of_clauses:                     0
% 8.04/1.51  res_num_in_passive:                     0
% 8.04/1.51  res_num_in_active:                      0
% 8.04/1.51  res_num_of_loops:                       77
% 8.04/1.51  res_forward_subset_subsumed:            514
% 8.04/1.51  res_backward_subset_subsumed:           4
% 8.04/1.51  res_forward_subsumed:                   0
% 8.04/1.51  res_backward_subsumed:                  0
% 8.04/1.51  res_forward_subsumption_resolution:     0
% 8.04/1.51  res_backward_subsumption_resolution:    0
% 8.04/1.51  res_clause_to_clause_subsumption:       6775
% 8.04/1.51  res_orphan_elimination:                 0
% 8.04/1.51  res_tautology_del:                      201
% 8.04/1.51  res_num_eq_res_simplified:              0
% 8.04/1.51  res_num_sel_changes:                    0
% 8.04/1.51  res_moves_from_active_to_pass:          0
% 8.04/1.51  
% 8.04/1.51  ------ Superposition
% 8.04/1.51  
% 8.04/1.51  sup_time_total:                         0.
% 8.04/1.51  sup_time_generating:                    0.
% 8.04/1.51  sup_time_sim_full:                      0.
% 8.04/1.51  sup_time_sim_immed:                     0.
% 8.04/1.51  
% 8.04/1.51  sup_num_of_clauses:                     405
% 8.04/1.51  sup_num_in_active:                      167
% 8.04/1.51  sup_num_in_passive:                     238
% 8.04/1.51  sup_num_of_loops:                       180
% 8.04/1.51  sup_fw_superposition:                   6818
% 8.04/1.51  sup_bw_superposition:                   6585
% 8.04/1.51  sup_immediate_simplified:               9017
% 8.04/1.51  sup_given_eliminated:                   3
% 8.04/1.51  comparisons_done:                       0
% 8.04/1.51  comparisons_avoided:                    0
% 8.04/1.51  
% 8.04/1.51  ------ Simplifications
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  sim_fw_subset_subsumed:                 145
% 8.04/1.51  sim_bw_subset_subsumed:                 0
% 8.04/1.51  sim_fw_subsumed:                        506
% 8.04/1.51  sim_bw_subsumed:                        1
% 8.04/1.51  sim_fw_subsumption_res:                 0
% 8.04/1.51  sim_bw_subsumption_res:                 0
% 8.04/1.51  sim_tautology_del:                      2
% 8.04/1.51  sim_eq_tautology_del:                   1801
% 8.04/1.51  sim_eq_res_simp:                        0
% 8.04/1.51  sim_fw_demodulated:                     5764
% 8.04/1.51  sim_bw_demodulated:                     49
% 8.04/1.51  sim_light_normalised:                   5706
% 8.04/1.51  sim_joinable_taut:                      0
% 8.04/1.51  sim_joinable_simp:                      0
% 8.04/1.51  sim_ac_normalised:                      0
% 8.04/1.51  sim_smt_subsumption:                    0
% 8.04/1.51  
%------------------------------------------------------------------------------
